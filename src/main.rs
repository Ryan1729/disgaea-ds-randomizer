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

    const FIRST_DSARCIDX_START: Addr = 0x000F_C600;

    mod dsarcidx {
        pub const MAGIC: &[u8] = b"DSARCIDX";
    }

    rom.seek(SeekFrom::Start(u64::from(FIRST_DSARCIDX_START)))?;

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

    #[repr(C)]
    #[derive(Debug)]
    struct FileEntry<const BASE: Addr> {
        file_name: FileName,
        size: AddrOffset,
        offset: AddrOffset,
    }

    impl <const BASE: Addr> FileEntry<BASE> {
        fn addr(&self) -> Addr {
            BASE + self.offset
        }

        fn after(&self) -> Addr {
            self.addr() + self.size
        }
    }

    // Assert that there is no struct padding
    compile_time_assert!{
        size_of::<FileEntry<0>>()
        == (
            size_of::<FileName>()
            + size_of::<u32>()
            + size_of::<u32>()
        )
    }

    let mut entries: Vec<FileEntry<FIRST_DSARCIDX_START>>
        // + 1 in case we need to add an entry for
        = Vec::with_capacity((entry_count + 1) as _);

    for _ in 0..entry_count {
        let mut buffer = [0u8; size_of::<FileEntry<0>>()];

        rom.read_exact(&mut buffer)?;

        // SAFETY: FileEntry has no padding, and all bit values are valid.
        let entry = unsafe {
            core::mem::transmute::<
                [u8; size_of::<FileEntry<FIRST_DSARCIDX_START>>()],
                FileEntry<FIRST_DSARCIDX_START>,
            >(buffer)
        };

        entries.push(entry);
    }

    assert_eq!(entries.len(), entry_count as _);

    let mut max_after: Addr = 0;

    for entry in entries {
        let after = entry.after();
dbg!(std::str::from_utf8(&entry.file_name), after);
        if after > max_after {
            max_after = after;
        }
    }

    println!(
        "{max_after:#010X}"
    );

    std::fs::write(output_path, rom.get_ref())
        .map_err(From::from)
}
