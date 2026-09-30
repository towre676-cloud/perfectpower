# Packaging validation

Validated on September 30, 2026 with Python 3.12.14.

All 69 raw source files pass upstream Git blob SHA1, exact byte-length, and SHA256 verification. Their total raw size is 25,602,686 bytes. The original CRLF line endings in relevant cvc5 files are retained. The upstream cvc5 COPYING and AUTHORS files were also checked against their Git blob hashes before packaging.

The ELSTER selector was independently recomputed from the complete 181-file index and matches the 19 bundled files across all 19 available strata. The cvc5 scan index contains 292 SMT2 paths and marks 49 included paths. Inspection completed with zero parse errors and reports 12,860 check-sat/check-sat-assuming commands in total.

The safety checks pass for comments and multiline metadata, quoted strings, exact polynomial normalization, sort-aware symbol use, rejection beneath Boolean context barriers, unsupported division, self-dependent right-hand sides, and malformed parentheses. All five tool source files compile. Both runner and acquisition CLI help paths work, and the baseline runner refuses a missing solver with an explicit error.

Packaging checks include a complete SHA256 manifest excluding the manifest itself, ZIP CRC validation, strict size enforcement below 30,000,000 bytes, extraction into a temporary directory, and successful re-verification from that extracted directory. The ZIP contains no Python bytecode, solver binary, access token, or repository working checkout.

No Z3/cvc5 solver was installed or executed. No independent performance baseline, PerfectPower compilation of these inputs, Lean/Mathlib build, proof checking, downstream integration, or PowerShell execution was performed. The bundled reports are structural inspection and provenance evidence only. The remaining validation work is specified in `CLAUDE_CODE_START_HERE.md`.
