use std::io::{
    Seek,
    SeekFrom,
    Read,
    Write,
};

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

    const DSARC_FL_START: Addr = 0x000C_829C;
    const DSARC_FL_MAGIC: &[u8] = b"DSARC FL\0";
    const DSARCIDX_MAGIC: &[u8] = b"DSARCIDX\0";

    rom.seek(SeekFrom::Start(u64::from(DSARC_FL_START)))?;

    {
        let mut buffer = [0; DSARC_FL_MAGIC.len()];

        rom.read_exact(&mut buffer)?;

        if buffer != DSARC_FL_MAGIC {
            Err(format!(
                "Expected {} at {:#010X}, got {}",
                HexSlice(DSARC_FL_MAGIC),
                Addr::try_from(rom.position())?,
                HexSlice(&buffer),
            ))?;
        }
    }

    {
        let mut buffer = [0; DSARCIDX_MAGIC.len()];

        rom.read_exact(&mut buffer)?;

        if buffer != DSARCIDX_MAGIC {
            Err(format!(
                "Expected {} at {:#010X}, got {}",
                HexSlice(DSARCIDX_MAGIC),
                Addr::try_from(rom.position())?,
                HexSlice(&buffer),
            ))?;
        }
    }

    std::fs::write(output_path, rom.get_ref())
        .map_err(From::from)
}
