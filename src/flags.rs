use xs::Seed;

#[derive(Default)]
pub enum Mode {
    #[default]
    ItemShuffle,
    YoshitsunaWristband,
    // Reminder, when updating these, update the CLI docs below!
}

pub struct Spec {
    pub seed: Seed,
    pub mode: Mode,
}

xflags::xflags! {
    cmd args {
        /// The PRNG seed to use. If not specified, one will be chosen based on the
        /// current time.
        optional seed: String
        /// The randomization mode to use.
        /// Valid values are:
        /// * item-shuffle
        /// * yoshitsuna-wristband
        /// If not specified, item-shuffle is the default
        optional mode: String
    }
}

#[derive(Debug)]
pub enum Error {
    InvalidSeed(String),
    UnknownMode(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use Error::*;
        match self {
            InvalidSeed(non_seed) => write!(f, "\"{non_seed}\" is not a valid seed."),
            UnknownMode(non_mode) => write!(f, "\"{non_mode}\" is not a known mode."),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use Error::*;
        match self {
            InvalidSeed(_)
            | UnknownMode(_) => None,
        }
    }
}

impl Args {
    fn to_spec(self) -> Result<Spec, Error> {
        use Error::*;
        let seed = match self.seed {
            Some(seed_string) => {
                u128::from_str_radix(&seed_string, 10)
                    .map_err(|_| InvalidSeed(seed_string))?
                    .to_le_bytes()
            }
            None => {
                let time = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default();
                let time = time.as_secs_f64();
            
                // SAFETY: These two types have no padding and every bit pattern is
                // valid for them.
                unsafe {
                    core::mem::transmute::<[f64; 2], [u8; 16]>([time, 1.0 / time])
                }
            }
        };

        let mode = match self.mode.as_deref() {
            None => Mode::default(),
            Some("item-shuffle") => Mode::ItemShuffle,
            Some("yoshitsuna-wristband") => Mode::YoshitsunaWristband,
            Some(s) => {
                return Err(UnknownMode(s.to_owned()))
            }
        };

        Ok(Spec {
            seed,
            mode,
        })
    }
}

type Res<A> = Result<A, Box<dyn std::error::Error>>;

pub fn spec() -> Res<Spec> {
    let args = Args::from_env()?;

    args.to_spec()
        .map_err(From::from)
}