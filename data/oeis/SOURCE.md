# OEIS entries used by PerfectPower

The `.seq` files under `seq/` are **unmodified copies** of entries of the On-Line Encyclopedia of
Integer Sequences (https://oeis.org), taken from the official Git export
https://github.com/oeis/oeisdata. The export commit and its `time.txt` are recorded in
`manifest.json`, together with the SHA-256 of every file. `make verify` checks those hashes.

The OEIS is copyrighted by the OEIS Foundation and made available under the Creative Commons
Attribution Share Alike 4.0 license (https://creativecommons.org/licenses/by-sa/4.0/). Each entry
keeps its own authorship lines. These files are distributed here under the same license. The
rest of the repository keeps its own license.

`discovery_sqrt2.json` lists the candidate coordinate maps. They were found by a term-index
search of every OEIS entry; the index came from the same export, dated 2026-09-29 (see
`manifest.json`, `global_index`). The index itself is not committed. Matching terms is only a
lead. The outcome of each candidate, and the Lean theorem when there is one, is in
`receipts/oeis_sqrt2_atlas.json`.
