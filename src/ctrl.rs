/// A `Ctrl` represents a slot. It either flags
/// the slot as unoccupied, or contains the h2
/// hash of the element that occupies it.
#[derive(Clone, Copy)]
pub union Ctrl {
    pub flag: Flag,
    pub h2: u8,
}

impl From<Ctrl> for u8 {
    fn from(c: Ctrl) -> u8 {
        unsafe {
            match c {
                Ctrl { h2 } => h2,
            }
        }
    }
}

impl From<Flag> for Ctrl {
    fn from(flag: Flag) -> Self {
        Self { flag }
    }
}

impl From<u8> for Ctrl {
    fn from(h2: u8) -> Self {
        Self { h2 }
    }
}

impl From<u64> for Ctrl {
    fn from(hash: u64) -> Self {
        Self {
            h2: (hash & 0x7F) as u8,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Flag {
    Empty = 0x80,
    Deleted = 0xFF,
}
