# Replaying the Petersen50 counting certificate

The source-bound Boolean decision diagram (BDD) certificate establishes a feasible-subset population of **702,508,860,122,761** for the 50-project, five-resource instance in the literal OR-Library dataset `data/planning/mknap1.txt`. The checker parses those capacities and costs, verifies the deterministic coordinate permutation, and checks the threshold proofs, conjunction chain, exact node populations and finalization. Replay consumes the existing witness with the Python standard library. Use a 64-bit Linux environment, including WSL, with Python 3.12, `unzip`, GNU `sha256sum`, and at least 1 GB of free disk for the downloaded ZIP and extracted xz member. The raw stream is decompressed in memory in blocks and does not need a separate disk copy.

## Retrieve the witness

Download [PerfectPower_Petersen_SourceBound_Verification.zip](https://chatgpt.com/library?file_id=libfile_d3a6b80e4b988191a38fea8c46cfc619&account_id=personal). The existing download was verified through the owning account on November 10, 2026. Access for unauthenticated readers has not been verified. GitHub carries the source, this evidence index and receipts. On November 10, the GitHub releases API returned an empty list and the live research endpoint exposed a result receipt without a witness download. The witness is the ZIP member `perfectpower/certs/planning/petersen50.trace.xz`.

| File or stream | Bytes | SHA-256 |
| --- | ---: | --- |
| Original ZIP | 469,886,735 | `20bc53f2bfad4c4b2a585922ded144bed20d777f6b7143ad81b2145a3e1d0413` |
| Complete compressed witness | 394,402,476 | `bbfa02d1651d4bd7edc3056da412dd514c4de4dd8364688619b9b4894f858354` |
| Uncompressed proof stream | 1,395,583,020 | `3ed96863081f6ba5c00eab09869034bcf1b42a0d16b45836b63fd30c6975d5ed` |

The ZIP's published source snapshot is [82daeac0600b](https://github.com/towre676-cloud/perfectpower/tree/82daeac0600b7b6555b2dd652e524664bb09e550). All six replay inputs in the [SHA-256 manifest](../receipts/planning/independent/petersen50-replay.sha256) match byte for byte in that snapshot, the ZIP, the [reviewed main commit](https://github.com/towre676-cloud/perfectpower/tree/408744741bd3ef1a56987e1888f90c85a16bf149) and the [reviewed PR #17 head](https://github.com/towre676-cloud/perfectpower/tree/8ce26bed932c6f30655bb276ded5b59fd80db542). The manifest includes the command-line entry point, checker, dataset parser, raw dataset, package initializer and the initializer's `core.py` import. The historical C search, the BDD producer, compiler and Lean are outside the replay dependencies.

## Run the canonical checker

Start with the ZIP and a copy of `petersen50-replay.sha256` in the current directory. Run the following in a fresh working directory. It extracts only the pinned inputs, expected receipt and witness.

```bash
set -eu
archive="$PWD/PerfectPower_Petersen_SourceBound_Verification.zip"
manifest="$PWD/petersen50-replay.sha256"
printf '%s  %s\n' \
  20bc53f2bfad4c4b2a585922ded144bed20d777f6b7143ad81b2145a3e1d0413 \
  "$archive" | sha256sum --check
mkdir petersen50-replay
cd petersen50-replay
while read -r checksum path; do
  mkdir -p "$(dirname "$path")"
  unzip -p "$archive" "perfectpower/$path" > "$path"
done < "$manifest"
sha256sum --check "$manifest"

unzip -p "$archive" perfectpower/certs/planning/petersen50.trace.xz \
  > petersen50.trace.xz
printf '%s  %s\n' \
  bbfa02d1651d4bd7edc3056da412dd514c4de4dd8364688619b9b4894f858354 \
  petersen50.trace.xz | sha256sum --check

unzip -p "$archive" perfectpower/receipts/planning/independent/certificate50.json \
  > certificate50.expected.json
python3 scripts/check_planning_certificate.py petersen50.trace.xz \
  --case 50 --receipt certificate50.fresh.json
python3 - <<'PY'
import json
from pathlib import Path

expected = json.loads(Path("certificate50.expected.json").read_text())
actual = json.loads(Path("certificate50.fresh.json").read_text())
expected.pop("seconds")
elapsed = actual.pop("seconds")
if actual != expected or actual["count"] != 702508860122761:
    raise SystemExit("Petersen50 receipt mismatch")
print(f"Petersen50 receipt matched ({elapsed:.3f} seconds)")
PY
```

The comparison includes the literal-source and checker hashes, complete coordinate order, compressed and uncompressed hashes, raw length and result. It excludes wall time. Expect `records_by_tag` of `[14404146, 20391, 29187394, 5, 1]`, in the order nonterminal allocations, threshold proofs, conjunction proofs, resource stages and finalization. The checker reports 14,404,148 allocated nodes including the two terminals.

Given the exact xz file separately, the same checker command works from a pinned checkout with the six source hashes verified. The matching [canonical receipt](../receipts/planning/independent/certificate50.json) can supply the expected JSON.

## Evidence boundaries

| Evidence | What it establishes |
| --- | --- |
| [Original publication receipt](../receipts/planning/independent/certificate_publication.json) and [checker output](../receipts/planning/independent/certificate50.json) | Original ZIP identity and the initial replay of the complete source-bound trace. |
| [November 10 replay](../receipts/planning/independent/certificate50_retrieval_replay.json) | Fresh checker output from the recovered ZIP and six pinned inputs. Replay finished in 166.933 seconds with CPython 3.12.14. Every other receipt field matches the original publication and the earlier PR #17 replay. |
| [PR #17 compiled audit](PETERSEN50_REPRODUCIBILITY_AUDIT.md) | Preserves the historical search materials and a separate earlier BDD replay. The accounting command regenerates bounded depth-13 splits and aggregates historical solved-prefix counts into partial intervals. |
| Historical best-first campaign | The closing log and result JSON record 24,921,515,942 expansions. The original final `bf50/state.bin` remains missing. The campaign and its solved-prefix counts were not independently re-executed by the BDD checker or the accounting reconstruction. |
| Lean | Local rules and small source-bound examples have separate proofs. The full result still depends on the Python parsing, packed table and checking implementation. The complete stream, table invariants and transport back to the original coordinates have yet to be connected in a full kernel proof. |
