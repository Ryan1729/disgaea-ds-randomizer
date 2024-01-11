use xs::Seed;

#[derive(Default)]
pub enum ItemShuffleKind {
    #[default]
    All,
    NonInitialShop,
}

pub enum RandomizationMode {
    ItemShuffle(ItemShuffleKind),
    YoshitsunaWristband,
    HorseWienerWristband,
    // Reminder, when updating these, update the CLI docs below!
}

impl Default for RandomizationMode {
    fn default() -> Self {
        Self::ItemShuffle(<_>::default())
    }
}

#[derive(Default)]
pub enum ItemNameMode {
    #[default]
    Maintain,
    Obscure,
    Rank,
    // Reminder, when updating these, update the CLI docs below!
}

pub struct Spec {
    pub seed: Seed,
    pub mode: RandomizationMode,
    pub item_name_mode: ItemNameMode,
}

xflags::xflags! {
    cmd args {
        /// The PRNG seed to use. If not specified, one will be chosen based on the
        /// current time.
        optional --seed seed: String
        /// The randomization mode to use.
        /// Valid values are:
        /// * item-shuffle
        /// * yoshitsuna-wristband
        /// * horse-wiener-wristband
        /// If not specified, item-shuffle is the default
        optional --mode mode: String
        /// The item name mode to use.
        /// Valid values are:
        /// * maintain
        /// * obscure
        /// * rank
        /// If not specified, maintain is the default
        optional --item-name-mode item_name_mode: String
    }
}

#[derive(Debug)]
pub enum Error {
    InvalidSeed(String),
    UnknownMode(String),
    UnknownItemNameMode(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use Error::*;
        match self {
            InvalidSeed(non_seed) => write!(f, "\"{non_seed}\" is not a valid seed."),
            UnknownMode(non_mode) => write!(f, "\"{non_mode}\" is not a known mode."),
            UnknownItemNameMode(non_mode) => write!(f, "\"{non_mode}\" is not a known item name mode."),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use Error::*;
        match self {
            InvalidSeed(_)
            | UnknownMode(_)
            | UnknownItemNameMode(_) => None,
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
            None => RandomizationMode::default(),
            Some("item-shuffle") => RandomizationMode::ItemShuffle(ItemShuffleKind::All),
            Some("item-shuffle-after-start") => RandomizationMode::ItemShuffle(ItemShuffleKind::NonInitialShop),
            Some("yoshitsuna-wristband") => RandomizationMode::YoshitsunaWristband,
            Some("horse-wiener-wristband") => RandomizationMode::HorseWienerWristband,
            Some(s) => {
                return Err(UnknownMode(s.to_owned()))
            }
        };

        let item_name_mode = match self.item_name_mode.as_deref() {
            None => ItemNameMode::default(),
            Some("maintain") => ItemNameMode::Maintain,
            Some("obscure") => ItemNameMode::Obscure,
            Some("rank") => ItemNameMode::Rank,
            Some(s) => {
                return Err(UnknownItemNameMode(s.to_owned()))
            }
        };

        Ok(Spec {
            seed,
            mode,
            item_name_mode,
        })
    }
}

type Res<A> = Result<A, Box<dyn std::error::Error>>;

pub fn spec() -> Res<Spec> {
    let args = match Args::from_env() {
        Ok(args) => args,
        Err(err) => err.exit(),
    };

    args.to_spec()
        .map_err(From::from)
}