Exact Charon extraction snapshots

manifest.json maps original paths relative to SignalReference to content-addressed,
deterministic gzip files. Both compressed and original SHA-256 hashes are checked.
The collection includes original inputs, selected inputs, and rejected experiments;
presence in this archive does not establish extraction or proof acceptance. Consult
each work directory's assessment, selection metadata, proof report and root review.

The raw .llbc files are ignored by Git because some exceed 100 MB. They have not
been deleted. This archive preserves their exact bytes independently of availability
of the pinned/cached Rust and Charon toolchains. It does not replace the source pins,
extraction commands or computational-body comparisons that establish provenance.

Verify all snapshots:
  python3 SignalReference/LLBCSnapshots/snapshot.py verify

Restore missing raw files before rerunning extraction audits:
  python3 SignalReference/LLBCSnapshots/snapshot.py restore

Restoration refuses to overwrite different existing content. Optional --only selects
one manifest path; --destination chooses a separate restoration directory. The
create command captures the current extraction inputs and verifies their round trip;
review any resulting manifest changes before committing them.

Initial checkpoint: 124 paths, deduplicated to 15,980,565 compressed bytes. All
round-trip hashes checked; restoration and refusal to overwrite a conflicting file
were exercised using a temporary directory. Build products and downloaded translator
source trees are excluded. Generated Lean, source/selection patches, proof reports,
licenses and pinned dependency metadata are retained separately in Git.
