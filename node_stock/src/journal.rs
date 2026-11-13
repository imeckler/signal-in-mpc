//! The consumed journal, exactly as `TlsMpc/Node/Stock/Journal.lean` models it.
//!
//! Records of 16 bytes: the watermark `w` (u64 little-endian: every index up to and including
//! `w` is consumed) and an 8-byte check `journal_tag(stock_id, w)`. The next usable index is one
//! more than the largest watermark. Reading (`parse`): complete records in order; a final
//! fragment shorter than a record is a torn tail and is dropped (Lean `parse_prefix`); a complete
//! record with a wrong check is corruption and the stock is refused. Opening a journal truncates
//! a torn tail and syncs (the restart of Lean `Journal.crash`), so the next append is aligned.

use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

use crate::format::journal_tag;

pub const REC_LEN: usize = 16;

/// A complete record whose check fails: not something a crash produces (Journal.lean).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Corrupt;

/// `encRec`.
pub fn enc_rec(stock_id: &[u8; 32], w: u64) -> [u8; REC_LEN] {
    let mut r = [0u8; REC_LEN];
    r[..8].copy_from_slice(&w.to_le_bytes());
    r[8..].copy_from_slice(&journal_tag(stock_id, w));
    r
}

/// `parse`: the entries of the complete records; a torn tail is dropped.
pub fn parse(stock_id: &[u8; 32], bytes: &[u8]) -> Result<Vec<u64>, Corrupt> {
    let mut out = Vec::with_capacity(bytes.len() / REC_LEN);
    for rec in bytes.chunks_exact(REC_LEN) {
        let w = u64::from_le_bytes(rec[..8].try_into().expect("8 bytes"));
        if rec[8..] != journal_tag(stock_id, w) {
            return Err(Corrupt);
        }
        out.push(w);
    }
    Ok(out)
}

/// `nextOf`: one more than the largest entry (0 when empty). Saturates at u64::MAX.
pub fn next_of(entries: &[u64]) -> u64 {
    entries.iter().map(|&w| w.saturating_add(1)).max().unwrap_or(0)
}

/// An open journal file.
pub struct JournalFile {
    file: File,
    stock_id: [u8; 32],
    /// Bytes in the file (whole records).
    len: u64,
    next: u64,
}

impl JournalFile {
    /// Create an empty journal (replacing any file there) and sync it.
    pub fn create(path: &Path, stock_id: [u8; 32]) -> io::Result<JournalFile> {
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(path)?;
        file.sync_all()?;
        Ok(JournalFile { file, stock_id, len: 0, next: 0 })
    }

    /// Open an existing journal: read it, drop a torn tail (truncate and sync).
    pub fn open(path: &Path, stock_id: [u8; 32]) -> io::Result<Result<JournalFile, Corrupt>> {
        let mut file = OpenOptions::new().read(true).write(true).open(path)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        let entries = match parse(&stock_id, &bytes) {
            Ok(e) => e,
            Err(c) => return Ok(Err(c)),
        };
        let whole = (entries.len() * REC_LEN) as u64;
        if whole != bytes.len() as u64 {
            file.set_len(whole)?;
            file.sync_all()?;
        }
        Ok(Ok(JournalFile { file, stock_id, len: whole, next: next_of(&entries) }))
    }

    /// Append a watermark (written, not yet durable).
    pub fn append(&mut self, w: u64) -> io::Result<()> {
        self.file.seek(SeekFrom::Start(self.len))?;
        self.file.write_all(&enc_rec(&self.stock_id, w))?;
        self.len += REC_LEN as u64;
        self.next = self.next.max(w.saturating_add(1));
        Ok(())
    }

    /// Make everything appended durable (fsync).
    pub fn sync(&mut self) -> io::Result<()> {
        self.file.sync_data()
    }

    pub fn next(&self) -> u64 {
        self.next
    }

    pub fn len(&self) -> u64 {
        self.len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file_of(stock: &[u8; 32], es: &[u64]) -> Vec<u8> {
        es.iter().flat_map(|&w| enc_rec(stock, w)).collect()
    }

    /// Lean `parse_prefix`: every prefix, cut at any byte, reads as the records it contains.
    #[test]
    fn parse_every_prefix() {
        let stock = [7u8; 32];
        let es = [0u64, 1, 4, 5, 9, 10, u64::MAX - 1];
        let f = file_of(&stock, &es);
        for n in 0..=f.len() {
            assert_eq!(parse(&stock, &f[..n]), Ok(es[..n / REC_LEN].to_vec()), "cut at {n}");
        }
    }

    #[test]
    fn corruption_refused() {
        let stock = [7u8; 32];
        let mut f = file_of(&stock, &[0, 1, 2]);
        f[20] ^= 1;
        assert_eq!(parse(&stock, &f), Err(Corrupt));
        // a journal of another stock fails its checks
        assert_eq!(parse(&[8u8; 32], &file_of(&stock, &[0])), Err(Corrupt));
        // zeros (what an unsynced extension may read as after a power loss) are refused, not read
        assert_eq!(parse(&stock, &[0u8; 16]), Err(Corrupt));
    }

    #[test]
    fn next_is_max_plus_one() {
        assert_eq!(next_of(&[]), 0);
        assert_eq!(next_of(&[3, 1, 2]), 4);
        assert_eq!(next_of(&[u64::MAX]), u64::MAX);
    }
}
