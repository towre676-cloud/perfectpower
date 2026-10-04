# Native Runge verification receipts

`lean_audit.log` records 79 declarations checked against the three standard axioms, 16 complete finite packets, two certificate-only cases and two exact-square families. The audit includes six mathematical rejection cases and false-packet/identity checks. `timing.json` measures the seven-module focused rebuild and audit. `summary.json` identifies the exact proof inputs, pinned toolchain and limits of verification.

The CLI logs retain the complete build-and-solve entry point, standalone sextic source, exact-square branch and a huge-bound certificate without evaluating its finite search. `cli_input_validation.json` records seven accepted or rejected shell input cases. `python_tests.log` records all 525 Python tests, with four skips. Neither the full historical root rebuild nor hosted runner availability is claimed.
