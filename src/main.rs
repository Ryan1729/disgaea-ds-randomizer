use std::io::{
    Seek,
    SeekFrom,
    Read,
    Write,
};

use core::mem::size_of;

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

fn main() -> Res<()> {
    let input_path = "baserom.nds";
    let output_path = "output.nds";

    let mut rom = std::io::Cursor::new(
        std::fs::read(input_path)?
    );

    type Addr = u32;
    type AddrOffset = u32;

    //const FIRST_DSARCIDX_START: Addr = 0x000F_C600;
    const TABLE_DSARCIDX_START: Addr = 0x03DE_2800;

    mod dsarcidx {
        pub const MAGIC: &[u8] = b"DSARCIDX";
    }

    rom.seek(SeekFrom::Start(u64::from(TABLE_DSARCIDX_START)))?;

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
        macro_rules! read_u32 {
            () => ({
                let mut buffer = [0; 4];

                rom.read_exact(&mut buffer)?;

                u32::from_le_bytes(buffer)
            })
        }

        entry_count = read_u32!();
dbg!(entry_count);
        assert!(entry_count > 0);

        // A field of unknown purpose which is always 0.
        // (Maybe reserved for a file type version number?)
        let _version = read_u32!();

        let ids_length: AddrOffset =
            // 2 bytes for each ID
            2 * entry_count;

        rom.seek(SeekFrom::Current(
            i64::from(ids_length)
        ))?;

        rom.set_position(
            (
                rom.position()
                // Add and AND to align to 4 byte boundary
                + (4 - 1)
            ) & !(4 - 1)
        );

    }

    type FileName = [u8; 40];

    const ZERO_FILE_NAME: FileName = [0; 40];

    macro_rules! no_padding_def {
        // As of this writing, we plan to support only enough generics stuff to
        // define what we actually need to.
        (
            struct $name: ident $(< const $base_name: ident : $base_type: ty >)? {
                $($field_name: ident : $field_type: ty),+
                $(,)?
            }

            $( $type_instance_suffix: tt )*
        ) => {
            #[repr(C)]
            #[derive(Debug)]
            struct $name <$(const $base_name: $base_type)?> {
                $($field_name: $field_type),+
            }

            // Assert that there is no struct padding
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
        }
    }

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

    let mut entries: Vec<FileEntry<TABLE_DSARCIDX_START>>
        // + 1 in case we need to add an entry for
        = Vec::with_capacity((entry_count + 1) as _);

    for _ in 0..entry_count {
        let mut buffer = [0u8; size_of::<FileEntry<0>>()];

        rom.read_exact(&mut buffer)?;

        // SAFETY: FileEntry has no padding, and all bit values are valid.
        let entry = unsafe {
            core::mem::transmute::<
                [u8; size_of::<FileEntry<TABLE_DSARCIDX_START>>()],
                FileEntry<TABLE_DSARCIDX_START>,
            >(buffer)
        };

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

    println!(
        "item_addr: {item_addr:#010X}"
    );

    if item_addr == 0 {
        Err(format!(
            "Could not find entry named {} starting from {:#010X}",
            nul_terminated_as_str(&ITEM_TABLE_FILE_NAME),
            TABLE_DSARCIDX_START,
        ))?;
    }

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
            pre: [u8; 0x16],
            name: [u8; 0x10],
            name_term: [u8; 0x1], // Always 0, seems like a nul terminator
            description: [u8; 0x50],
            description_term: [u8; 0x1], // Always 0, seems like a nul terminator
            rank: Rank,
            range: Range,
            flags: ItemFlags,
            type1: Type1,
            type2: Type2,
            post: [u8; 0x3],
        }
    }

    std::fs::write(output_path, rom.get_ref())
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