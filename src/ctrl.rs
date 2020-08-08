use std::fmt;

/// A `Ctrl` represents a slot. It either flags
/// the slot as unoccupied, or contains the h2
/// hash of the element that occupies it.
#[derive(Clone, Copy)]
#[repr(C, align(1))]
pub union Ctrl {
    pub flag: Flag,
    pub h2: u8,
}

impl From<Ctrl> for u8 {
    fn from(c: Ctrl) -> u8 {
        unsafe { c.h2 }
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

impl fmt::Debug for Ctrl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            match self {
                Ctrl { flag: Flag::Empty } => f.write_str("Empty"),
                Ctrl {
                    flag: Flag::Deleted,
                } => f.write_str("Deleted"),
                Ctrl { h2 } => f.write_str(&format!("Filled: {}", h2)),
            }
        }
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Flag {
    Empty = 0x80,
    Deleted = 0xFF,
}
