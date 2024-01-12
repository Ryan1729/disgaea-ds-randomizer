use core::mem::size_of;
use std::collections::BTreeMap;

mod flags;

use flags::{ItemShuffleKind, ItemNameMode, Spec};

macro_rules! compile_time_assert {
    ($assertion: expr) => {
        #[allow(unknown_lints, clippy::eq_op)]
        // Based on the const_assert macro from static_assertions.
        const _: [(); 0 - !{$assertion} as usize] = [];
    }
}

type Res<A> = Result<A, Box<dyn std::error::Error>>;

struct HexSlice<'slice>(&'slice [u8]);

impl core::fmt::Display for HexSlice<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.0.len() == 0 {
            return Ok(())
        }
        write!(f, "0x")?;

        // TODO? flip endianess with `:#`?

        for byte in self.0 {
            write!(f, "{byte:02X?}")?;
        }

        Ok(())
    }
}

type Addr = u32;
// We can make this signed, with some work, if we ever actually need to do reverse
// seeking.
type AddrOffset = u32;

/// Counts upwards with gaps, some of them significant.
/// Often the gaps are to or just past round decimal
/// values. If the list of items is not sorted
/// according to this, then items don't show up in shop
/// lists etc.
type SortKey = u16;

/// SAFETY: This macro assumes that bit values are valid for the defined type.
/// So if you define a type with booleans, for example, that is your own fault!
macro_rules! no_padding_def {
    // As of this writing, we plan to support only enough generics stuff to
    // define what we actually need to.
    (
        $vis:vis struct $name: ident $(< const $base_name: ident : $base_type: ty >)? {
            $($field_vis:vis $field_name: ident : $field_type: ty),+
            $(,)?
        }

        $( $type_instance_suffix: tt )*
    ) => {
        #[repr(C)]
        #[derive(Debug, Copy, Clone)]
        $vis struct $name <$(const $base_name: $base_type)?> {
            $($field_vis $field_name: $field_type),+
        }

        // Assert that there is no struct padding. This is a requirement of
        // `rom::PlainData`.
        compile_time_assert!{
            size_of::<$name $( $type_instance_suffix )* >()
            == {
                let sizes = [$(size_of::<$field_type>()),+];

                let mut sum = 0;
                let mut i = 0;
                while i < sizes.len() {
                    sum += sizes[i];
                    i += 1;
                }

                sum
            }
        }

        // SAFETY: We expect callers of the macro to ensure that all bit values
        // are valid for this type.
        unsafe impl <$(const $base_name: $base_type)?> rom::PlainData for $name <$($base_name)?> {}
    }
}

mod rom {
    use super::*;

    // There is at least one cast that assumes this to be the case.
    compile_time_assert!{
        usize::BITS >= Addr::BITS
    }

    /// A type large enough to hold the maximum amount of bytes that could be
    /// in the ROM, which implies that it is also large enough to hold the
    /// count of items in any slice of data from the ROM, including of
    /// multi-byte types.
    pub type SliceCount = u32;

    // There is at least one cast that assumes this to be the case.
    compile_time_assert!{
        usize::BITS >= SliceCount::BITS
    }

    /// A type similar to `std::io::Cursor` with the operations from that which we
    /// need, and some additional ones not from that type, which we also need.
    pub struct Rom<'data> {
        data: &'data mut [u8],
        position: Addr,
    }

    macro_rules! no_data_error_def {
        ($name: ident) => {
            #[derive(Clone, Copy, Debug)]
            pub struct $name;

            impl core::fmt::Display for $name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, stringify!($name))
                }
            }

            impl std::error::Error for $name {}
        }
    }

    no_data_error_def!{BufferTooLongError}

    impl Rom<'_> {
        pub fn new(data: &mut [u8]) -> Result<Rom, BufferTooLongError> {
            let _ = AddrOffset::try_from(data.len())
                .map_err(|_| BufferTooLongError)?;
            Ok(Rom {
                data,
                position: 0,
            })
        }

        fn one_past_end(&self) -> Addr {
            AddrOffset::try_from(self.data.len())
                .expect("A Rom with a too long data field should not be possible, by construction.")
        }
    }

    impl Rom<'_> {
        fn remaining(&self) -> &[u8] {
            &self.data[self.position as usize..]
        }

        pub fn position(&self) -> Addr {
            self.position
        }

        pub fn read_u32(&mut self) -> Result<u32, ReadExactError> {
            let mut buffer = [0; 4];

            self.read_exact(&mut buffer)?;

            Ok(u32::from_le_bytes(buffer))
        }
    }

    no_data_error_def!{PresumedImpossibleIOError}

    #[derive(Debug)]
    pub enum ReadExactError {
        OffsetTooLong(OffsetTooLongError),
        SeekFromCurrent(SeekFromCurrentError),
        Io(PresumedImpossibleIOError),
    }

    impl std::error::Error for ReadExactError {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            use ReadExactError::*;
            match self {
                OffsetTooLong(e) => Some(e),
                SeekFromCurrent(e) => Some(e),
                Io(e) => Some(e),
            }
        }
    }

    impl core::fmt::Display for ReadExactError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "ReadExactError")
        }
    }

    impl Rom<'_> {
        pub fn read_exact(&mut self, buffer: &mut [u8]) -> Result<(), ReadExactError> {
            let offset: AddrOffset = AddrOffset::try_from(buffer.len())
                .map_err(|_| ReadExactError::OffsetTooLong(OffsetTooLongError))?;

            let mut remaining = self.remaining();

            std::io::Read::read_exact(&mut remaining, buffer)
                // The current read_exact method for slices never errors.
                // Adding the std::io::Error to the API just for the small
                // chance that chnages seems undesireable.
                .map_err(|_| ReadExactError::Io(PresumedImpossibleIOError))?;

            self.seek_from_current(offset)
                .map_err(ReadExactError::SeekFromCurrent)
        }
    }

    no_data_error_def!{OffsetTooLongError}
    no_data_error_def!{BadAddrError}

    impl Rom<'_> {
        pub fn seek_from_start(&mut self, addr: Addr) -> Result<(), BadAddrError> {
            if addr >= self.one_past_end() {
                Err(BadAddrError)
            } else {
                self.position = addr;
                Ok(())
            }
        }
    }

    no_data_error_def!{BadOffsetError}

    #[derive(Debug)]
    pub enum SeekFromCurrentError {
        BadOffset(BadOffsetError),
        BadAddr(BadAddrError),
    }

    impl std::error::Error for SeekFromCurrentError {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            use SeekFromCurrentError::*;
            match self {
                BadOffset(e) => Some(e),
                BadAddr(e) => Some(e),
            }
        }
    }

    impl core::fmt::Display for SeekFromCurrentError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "SeekFromCurrentError")
        }
    }

    impl Rom<'_> {
        pub fn seek_from_current(&mut self, offset: AddrOffset) -> Result<(), SeekFromCurrentError> {
            match self.position.checked_add(offset) {
                Some(addr) => {
                    self.seek_from_start(addr)
                        .map_err(SeekFromCurrentError::BadAddr)
                }
                None => Err(SeekFromCurrentError::BadOffset(BadOffsetError)),
            }
        }
    }

    no_data_error_def!{SliceOffEndError}
    no_data_error_def!{UnexpectedPrefixError}
    no_data_error_def!{UnexpectedSuffixError}
    no_data_error_def!{UnexpectedSliceLengthError}

    #[derive(Clone, Copy, Debug)]
    pub enum SliceOfError {
        SliceOffEnd(SliceOffEndError),
        UnexpectedPrefix(UnexpectedPrefixError),
        UnexpectedSuffix(UnexpectedSuffixError),
        UnexpectedSliceLength(UnexpectedSliceLengthError),
    }

    impl std::error::Error for SliceOfError {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            use SliceOfError::*;
            match self {
                SliceOffEnd(e) => Some(e),
                UnexpectedPrefix(e) => Some(e),
                UnexpectedSuffix(e) => Some(e),
                UnexpectedSliceLength(e) => Some(e),
            }
        }
    }

    impl core::fmt::Display for SliceOfError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "SliceOfError")
        }
    }

    /// SAFETY: This must only be implemented on types with no padding or invalid
    /// bit patterns.
    pub unsafe trait PlainData {}

    impl Rom<'_> {
        // TODO? Could only take a non-zero SliceCount.
        pub fn mut_slice_of<A: PlainData>(
            &mut self,
            count: SliceCount
        ) -> Result<&mut [A], SliceOfError> {
            use SliceOfError::*;

            let count = count as usize;
            let len = size_of::<A>() * count;

            let position = self.position as usize;

            let one_past_end = match position.checked_add(len) {
                Some(one_past_end) if one_past_end <= self.data.len() => {
                    one_past_end
                }
                Some(_) | None => {
                    return Err(SliceOffEnd(SliceOffEndError));
                }
            };

            let byte_slice = &mut self.data[position..one_past_end];

            // SAFETY: This is safe given the implementor of `PlainData`
            // upholds the documented safety requirements.
            let (prefix, output, suffix) = unsafe {
                byte_slice.align_to_mut()
            };

            if !prefix.is_empty() {
                Err(UnexpectedPrefix(UnexpectedPrefixError))?;
            }

            if !suffix.is_empty() {
                Err(UnexpectedSuffix(UnexpectedSuffixError))?;
            }

            if output.len() != count {
                Err(UnexpectedSliceLength(UnexpectedSliceLengthError))?;
            }

            Ok(output)
        }
    }

    no_padding_def! {
        pub struct StringTableEntryAddr {
            adjusted_addr: Addr
        }
    }

    impl StringTableEntryAddr {
        fn addr(self) -> Addr {
            self.adjusted_addr
            // Seems like this offset is to account for the DS ram starting at
            // 0x0200_0000 for some reason.
            - 0x0200_0000
            // No idea why this offset of 0x4000 is needed, but it is.
            + 0x4000
        }

        pub fn from_addr(addr: Addr) -> Self {
            Self {
                adjusted_addr: addr
                    + 0x0200_0000
                    - 0x4000
            }
        }
    }

    no_padding_def! {
        pub struct StringTableEntry {
            pub sort_key: SortKey,
            pub pad: u16,
            pub addr: StringTableEntryAddr,
        }
    }

    pub struct StringTable<'rom> {
        pub strings: &'rom mut [u8],
        pub entries: &'rom mut [StringTableEntry],
    }

    impl core::fmt::Debug for StringTable<'_> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            if f.alternate() {
                let mut list = f.debug_list();
    
                for entry in self.entries.iter() {
                    list.entry(&self.get(entry.sort_key));
                }
    
                list.finish()
            } else {
                f.debug_struct("StringTable")
                .field("strings", &self.strings)
                .field("entries", &self.entries)
                .finish()
            }
        }
    }


    no_data_error_def!{StringTableGetError}

    impl StringTable<'_> {
        pub fn get_mut(&mut self, sort_key: SortKey) -> Result<&mut [u8], StringTableGetError> {
            self.entries
                .iter_mut()
                .find(|entry| entry.sort_key == sort_key)
                .ok_or(StringTableGetError)
                .map(|entry| {
                    let start_index = (entry.addr.addr() - ITEM_NAME_STRINGS_START)
                        as usize;

                    // Scan forward up to the nul terminator
                    let mut end_index = start_index;
                    for &byte in &self.strings[start_index..] {
                        if byte == b'\0' {
                            break;
                        }
                        end_index += 1;
                    }

                    &mut self.strings[start_index..end_index]
                })
        }

        // TODO? A test ensuring get and get_mut stay in sync?
        pub fn get(& self, sort_key: SortKey) -> Result<& [u8], StringTableGetError> {
            self.entries
                .iter()
                .find(|entry| entry.sort_key == sort_key)
                .ok_or(StringTableGetError)
                .map(|entry| {
                    let start_index = (entry.addr.addr() - ITEM_NAME_STRINGS_START)
                        as usize;

                    assert!(
                        start_index < self.strings.len(),
                        "{:#010X} @ {:#010X}({:#010X}) -> {:#010X}",
                        entry.sort_key,
                        entry.addr.addr(),
                        entry.addr.adjusted_addr,
                        start_index,
                    );

                    // Scan forward up to the nul terminator
                    let mut end_index = start_index;
                    for &byte in &self.strings[start_index..] {
                        if byte == b'\0' {
                            break;
                        }
                        end_index += 1;
                    }

                    & self.strings[start_index..end_index]
                })
        }
    }

    pub const ITEM_NAME_STRINGS_START: Addr = 0x0C_5D10;
    pub const ITEM_NAME_STRINGS_END: Addr = 0x0C_72F1;

    pub const ITEM_NAME_ENTRIES_START: Addr = 0x0C_72F4;
    pub const ITEM_NAME_ENTRIES_END: Addr = 0x0C_81E4;

    impl <'rom> Rom<'rom> {
        pub fn item_name_table(&'rom mut self) -> Result<StringTable<'rom>, SliceOfError> {
            use SliceOfError::*;

            assert!(
                ITEM_NAME_STRINGS_START < ITEM_NAME_STRINGS_END
                && ITEM_NAME_STRINGS_END <= ITEM_NAME_ENTRIES_START
                && ITEM_NAME_ENTRIES_START < ITEM_NAME_ENTRIES_END
            );

            let byte_slice: &mut [u8] = &mut self.data[
                ITEM_NAME_STRINGS_START as usize
                ..ITEM_NAME_ENTRIES_END as usize
            ];

            let (strings, entry_bytes) = byte_slice.split_at_mut(
                (ITEM_NAME_ENTRIES_START - ITEM_NAME_STRINGS_START) as usize
            );

            // Assert that StringTableEntry implments PlainData
            {
                compile_time_assert!{{
                    const fn entry_implements_plain_data() -> bool {
                        const fn implements_plain_data<T: PlainData>() {}

                        implements_plain_data::<StringTableEntry>();

                        true
                    }

                    entry_implements_plain_data()
                }}
            }

            // SAFETY: This is safe given the implementor of `PlainData`
            // upholds the documented safety requirements.
            let (prefix, entries, suffix) = unsafe {
                entry_bytes.align_to_mut()
            };

            if !prefix.is_empty() {
                Err(UnexpectedPrefix(UnexpectedPrefixError))?;
            }

            if !suffix.is_empty() {
                Err(UnexpectedSuffix(UnexpectedSuffixError))?;
            }

            let count = (ITEM_NAME_ENTRIES_END - ITEM_NAME_ENTRIES_START) as usize
                / size_of::<StringTableEntry>();

            if entries.len() != count {
                Err(UnexpectedSliceLength(UnexpectedSliceLengthError))?;
            }

            Ok(StringTable {
                strings,
                entries,
            })
        }
    }
}
use rom::{StringTableEntry, StringTableEntryAddr, Rom};

fn main() -> Res<()> {
    let Spec {
        seed,
        mode,
        item_name_mode,
        input_path,
        output_path,
    } = flags::spec()?;

    println!("Using {} as seed", u128::from_le_bytes(seed));

    let mut rng = xs::from_seed(seed);

    let mut rom_bytes = std::fs::read(input_path)?;

    let mut rom = Rom::new(
        &mut rom_bytes[..],
    )?;

    //const FIRST_DSARCIDX_START: Addr = 0x000F_C600;
    const TABLE_DSARCIDX_START: Addr = 0x03DE_2800;

    mod dsarcidx {
        pub const MAGIC: &[u8] = b"DSARCIDX";
    }

    rom.seek_from_start(TABLE_DSARCIDX_START)?;

    {
        let mut buffer = [0; dsarcidx::MAGIC.len()];

        rom.read_exact(&mut buffer)?;

        if buffer != dsarcidx::MAGIC {
            Err(format!(
                "Expected {} at {:#010X}, got {}",
                HexSlice(dsarcidx::MAGIC),
                Addr::try_from(rom.position())?,
                HexSlice(&buffer),
            ))?;
        }
    }

    // Advance to the end of the header
    let entry_count;
    {
        entry_count = rom.read_u32()?;

        assert!(entry_count > 0);

        // A field of unknown purpose which is always 0.
        // (Maybe reserved for a file type version number?)
        let _version = rom.read_u32()?;

        let ids_length: AddrOffset =
            // 2 bytes for each ID
            2 * entry_count;

        rom.seek_from_current(ids_length)?;

        rom.seek_from_start(
            (
                rom.position()
                // Add and AND to align to 4 byte boundary
                + (4 - 1)
            ) & !(4 - 1)
        )?;

    }

    type FileName = [u8; 40];

    const ZERO_FILE_NAME: FileName = [0; 40];

    no_padding_def! {
        struct FileEntry<const BASE: Addr> {
            file_name: FileName,
            size: AddrOffset,
            offset: AddrOffset,
        }

        <0>
    }

    impl <const BASE: Addr> FileEntry<BASE> {
        fn addr(&self) -> Addr {
            BASE + self.offset
        }

        #[allow(dead_code)]
        fn after(&self) -> Addr {
            self.addr() + self.size
        }
    }

    /// SAFETY: This macro assumes that the type has no padding, and that all bit
    /// values are valid.
    macro_rules! unsafe_read_type {
        ($type: ty) => ({
            let mut buffer = [0; size_of::<$type>()];

            rom.read_exact(&mut buffer)?;

            // SAFETY: $type has no padding, and all bit values are valid.
            unsafe {
                core::mem::transmute::<
                    [u8; size_of::<$type>()],
                    $type,
                >(buffer)
            }
        })
    }

    let mut entries: Vec<FileEntry<TABLE_DSARCIDX_START>>
        // + 1 in case we need to add an entry for
        = Vec::with_capacity((entry_count + 1) as _);

    for _ in 0..entry_count {
        // SAFETY: `FileEntry<TABLE_DSARCIDX_START>` has no padding, and all bit
        // values are valid.
        let entry = unsafe_read_type!(FileEntry<TABLE_DSARCIDX_START>);

        entries.push(entry);
    }

    assert_eq!(entries.len(), entry_count as _);

    const ITEM_TABLE_FILE_NAME: FileName = {
        let mut output = ZERO_FILE_NAME;

        let name = b"mitem.dat";
        let mut i = 0;
        while i < name.len() {
            output[i] = name[i];
            i += 1;
        }

        output
    };

    let mut item_addr: Addr = 0;

    for entry in entries {
        if entry.file_name == ITEM_TABLE_FILE_NAME {
            item_addr = entry.addr();
            break
        }
    }

    if item_addr == 0 {
        Err(format!(
            "Could not find entry named {} starting from {:#010X}",
            nul_terminated_as_str(&ITEM_TABLE_FILE_NAME),
            TABLE_DSARCIDX_START,
        ))?;
    }

    no_padding_def! {
        struct ItemTableHeader {
            // No idea why there's the number of entries
            // in the item table, twice.
            count1: u32,
            count2: u32,
        }
    }

    rom.seek_from_start(item_addr)?;

    // SAFETY: `ItemTableHeader` has no padding, and all bit values are valid.
    let item_table_header = unsafe_read_type!(ItemTableHeader);

    /// Set to:
    /// 0b1010 for Ultimate fist
    /// 0b0101 for Ultimate sword (Yoshitsuna)
    /// 0 for Ultimate spear (Glorious)
    /// 0 for Ultimate bow (Galaxy)
    type ItemFlags = u8;

    // Uusually 1 to 40, some exceptions are at 41 and 42.
    type Rank = u8;

    /// 0 for fist, 1 for sword, 2 for spear,
    /// 3 for most bows but switches to 4 on
    /// Remote Bow, (Rank 25)
    /// and rank 36 - 39.
    /// 5 for Ultimate bow (Galaxy)
    type Range = u8;

    /// 0 for fist, 1 for sword, 2 for spear, 3 for bows, 4 for guns
    type Type1 = u8;
    /// 1 for fist, 2 for sword, 3 for spear, 4 for bows, 5 for guns
    type Type2 = u8;

    no_padding_def! {
        struct Item {
            base_price: u32,
            sort_key: SortKey,
            hp: u16,
            sp: u16,
            atk: u16,
            def: u16,
            int: u16,
            spd: u16,
            hit: u16,
            res: u16,
            name: [u8; 0x10],
            name_term: [u8; 0x1], // Always 0, seems like a nul terminator
            description: [u8; 0x50],
            description_term: [u8; 0x1], // Always 0, seems like a nul terminator
            rank: Rank,
            range: Range,
            flags: ItemFlags,
            type1: Type1,
            type2: Type2,
            movement: u8,
            // Set to 21 to 25 for certain weapons with a chance of poison,
            // paralysis etc. effects.
            effect: u8,
            post: u8, // Always 0. Maybe just padding?
        }
    }

    // If these are different, then which is the one to use?
    assert_eq!(item_table_header.count1, item_table_header.count2);
    let item_count = item_table_header.count1;

    {
        use flags::RandomizationMode::*;
        let items: &mut [Item] = rom.mut_slice_of::<Item>(item_count)?;

        match mode {
            ItemShuffle(kind) => {
                use ItemShuffleKind::*;
                fn identity_mapper(i: u32) -> usize {
                    i as usize
                }

                const INITIAL_SHOP_INDEXES: [u32; 35] = [
                    // Weapons
                    0 * 40,
                    0 * 40 + 1, 
                    0 * 40 + 2,
                    1 * 40,
                    1 * 40 + 1, 
                    1 * 40 + 2,
                    2 * 40,
                    2 * 40 + 1, 
                    2 * 40 + 2,
                    3 * 40,
                    3 * 40 + 1, 
                    3 * 40 + 2,
                    4 * 40,
                    4 * 40 + 1,
                    4 * 40 + 2,
                    5 * 40,
                    5 * 40 + 1,
                    5 * 40 + 2,
                    6 * 40,
                    6 * 40 + 1,
                    6 * 40 + 2,
                    7 * 40,
                    7 * 40 + 1,
                    7 * 40 + 2,
                    // Armor
                    8 * 40,
                    8 * 40 + 1,
                    8 * 40 + 2,
                    // Use items
                    // HP
                    439,
                    439 + 1,
                    439 + 2,
                    // SP
                    449,
                    449 + 1,
                    449 + 2,
                    // Faerie Dust
                    470,
                    // Hands
                    471
                ];

                fn non_initial_shop_mapper(mut index: u32) -> usize {
                    while {
                        let mut is_initial_shop = false;
                        for &i in INITIAL_SHOP_INDEXES.iter() {
                            if i == index {
                                is_initial_shop = true;
                                break
                            }
                        }
                        is_initial_shop
                    } {
                        index += 1;
                    }

                    index as usize
                }

                let len = match kind {
                    All =>
                        items.len() as u32,
                    NonInitialShop => 
                        (items.len() - INITIAL_SHOP_INDEXES.len()) as u32,
                }; 

                xs::shuffle_with_swap(
                    &mut rng,
                    len,
                    |i1, i2| {
                        let (i1, i2) = match kind {
                            All => (
                                identity_mapper(i1),
                                identity_mapper(i2),
                            ),
                            NonInitialShop => (
                                non_initial_shop_mapper(i1),
                                non_initial_shop_mapper(i2),
                            ),
                        };

                        // TODO? Keep within categories to ensure all seeds are
                        // beatable without excessive grinding? Multiple options
                        // for how to split the categories?
                        // TODO? Multiple ptions on how to handle prices? Say
                        // keeping the prices of items the same as they would be
                        // without the shuffling?
                        // TODO Combine parts of the item structs together to make
                        // new, less balanced items.

                        // Maintain prices as they were before, so at least
                        // something will be affordable early on.
                        let base_price_1 = items[i1].base_price;
                        let base_price_2 = items[i2].base_price;

                        items.swap(i1, i2);

                        items[i1].base_price = base_price_1;
                        items[i2].base_price = base_price_2;
                    },
                )
            }
            YoshitsunaWristband => {
                let wristband_i = 0;
                let yoshitsuna_i = 79;
                items[yoshitsuna_i].base_price = 1;
                items.swap(wristband_i, yoshitsuna_i);
            },
            HorseWienerWristband => {
                let wristband_i = 0;
                let horse_wiener_i = 419;
                items[horse_wiener_i].base_price = 1;
                items.swap(wristband_i, horse_wiener_i);
            },
        }

        // Sort the sort_key values, in a slow but easy to write way.
        for i in 0..items.len() {
            let mut min_index = i;

            for j in i + 1..items.len() {
                if items[j].sort_key < items[min_index].sort_key {
                    min_index = j;
                }
            }

            // Found an element that wasn't in the proper place
            if min_index != i {
                let temp = items[min_index].sort_key;
                items[min_index].sort_key = items[i].sort_key;
                items[i].sort_key = temp;
            }
        }

        for item in items.iter() {
            // TODO proper spoiler file output
            println!(
                "{} ({} HL) {}",
                nul_terminated_as_str(&item.name),
                item.base_price,
                item.sort_key,
            );
        }

        match item_name_mode {
            ItemNameMode::Maintain => {
                // We assume that the names in the item list are the ones to use for
                // the given sort keys.
                let mut sort_key_to_name = BTreeMap::new();
                for item in items.iter() {
                    let insert_return = sort_key_to_name.insert(
                        item.sort_key,
                        item.name,
                    );

                    // Check that the key was not already in the map.
                    assert_eq!(insert_return, None);
                }

                compile_time_assert!(
                    size_of::<StringTableEntry>()
                    <= Addr::MAX as usize
                );

                {
                    let table = rom.item_name_table()?;

                    let mut char_i: u32 = 0;
                    let mut entry_i: u32 = 0;
                    for (sort_key, name) in sort_key_to_name {
                        let start_char_i = char_i;
                        for char in name {
                            table.strings[char_i as usize] = char;
                            char_i += 1;

                            if char == b'\0' {
                                break
                            }
                        }
                        let entry = &mut (table.entries[entry_i as usize]);

                        // The code could be changed to not assume this if needed.
                        // We'd just rewrite the sort key for each entry.
                        assert_eq!(entry.sort_key, sort_key);

                        entry.addr = StringTableEntryAddr::from_addr(
                            rom::ITEM_NAME_STRINGS_START
                            + start_char_i
                        );

                        entry_i += 1;
                    }
                }
            },
            ItemNameMode::Obscure => {
                for item in items.iter_mut() {
                    // These item names are apparently only used for the names of item world
                    // names apparently.
                    // TODO? Something funny here? Like funny in the context of it being
                    // "BLANK world"?
                    item.name = *(b"???\0\0\0\0\0\0\0\0\0\0\0\0\0");

                    // Set all descriptions to '???' after the type identification to
                    // obscure things slightly, and because that matches the replaced item
                    // names.
                    for i in 0..(item.description.len() - 4) {
                        if item.description[i] == b':' {
                            item.description[i + 1] = b'?';
                            item.description[i + 2] = b'?';
                            item.description[i + 3] = b'?';
                            item.description[i + 4] = b'\0';
                        }
                    }
                }

                // Replace the items strings with ??? because we know that will fit in every
                // case and that's easy to do. It might be nice to replace the strings with
                // different strings of varing lengths, but reverse-engineering how the string
                // table is used has turned out to be difficult.
                {
                    enum State {
                        InsertFirst,
                        InsertSecond,
                        InsertThird,
                        ScanForNul,
                    }
                    use State::*;
                    let mut state = InsertFirst;

                    for i in rom::ITEM_NAME_STRINGS_START..=rom::ITEM_NAME_STRINGS_END{
                        let i = i as usize;
                        state = match state {
                            InsertFirst => {
                                rom_bytes[i] = b'?';
                                InsertSecond
                            }
                            InsertSecond => {
                                rom_bytes[i] = b'?';
                                InsertThird
                            }
                            InsertThird => {
                                rom_bytes[i] = b'?';
                                ScanForNul
                            }
                            ScanForNul => {
                                if rom_bytes[i] == b'\0' {
                                    InsertFirst
                                } else {
                                    rom_bytes[i] = b'\0';
                                    ScanForNul
                                }
                            }
                        };
                    }
                }
            },
            ItemNameMode::Rank => {
                // We assume the rank in the items array is the correct one
                let mut sort_key_to_rank = BTreeMap::new();
                for item in items.iter() {
                    let insert_return = sort_key_to_rank.insert(
                        item.sort_key,
                        item.rank,
                    );

                    // Check that the key was not already in the map.
                    assert_eq!(insert_return, None);
                }

                {
                    let mut table = rom.item_name_table()?;

                    for (sort_key, rank) in sort_key_to_rank {
                        let entry: &mut [u8] = table.get_mut(sort_key)?;

                        assert!(entry.len() >= 3);
                        entry[0] = b'r';
                        entry[1] = b'0' + (rank / 10);
                        entry[2] = b'0' + (rank % 10);
                        for i in 3..entry.len() {
                            entry[i] = b'\0';
                        }
                    }
                }

                // We can leave the names in the item list alone for now, so players
                // can look up what the item name is if they want. If we add merged
                // items then we'll want to revisit this case
            },
        }
    }

    std::fs::write(output_path, &rom_bytes)
        .map_err(From::from)
}

fn nul_terminated_as_str<'slice>(
    bytes: &'slice [u8]
) -> &'slice str {
    let mut first_nul_index = 0;
    for &b in bytes {
        if b == b'\0' {
            break
        }
        first_nul_index += 1;
    }

    std::str::from_utf8(&bytes[0..first_nul_index])
        .unwrap_or("???")
}