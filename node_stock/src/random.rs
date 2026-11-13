//! Randomness for the boot id, stock ids and chain seeds: the operating system's generator.

use std::fs::File;
use std::io::{self, Read};

pub fn random32() -> io::Result<[u8; 32]> {
    let mut b = [0u8; 32];
    File::open("/dev/urandom")?.read_exact(&mut b)?;
    Ok(b)
}
