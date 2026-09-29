# Compiled structural continuation

Read `CLAUDE_CODE_HANDOFF.md` for application and integration instructions,
`MATHEMATICAL_CHAPTER.md` for the proofs and the next arithmetic obligations,
and `verification/results.json` for the actual verification receipt.

The new modules are opt-in: the baseline `PerfectPower.lean` root and its
169-declaration audit are unchanged. This overlay adds 31 theorem/lemma entries
and 9 directly audited definitions, using only standard axioms. Its existence
construction is noncomputable; the independent Python Yun algorithm is tested
but is not formally extracted from Lean.

Replay from the repository root:

```sh
python3 continuation_tools/verify.py
```

Lean must be available through the pinned `lean-toolchain`; Mathlib dependencies
must have been fetched. Follow the full integration gate in the handoff before
publishing updated global status counts.
