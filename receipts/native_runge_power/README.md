# Native higher-power Runge receipts

`lean_audit.log` records 124 declarations using only the three standard axioms, 20 complete finite packets, two certificate-only searches, three exact-power families, eight rejection cases and false-packet checks. `timing.json` measures the nine-module focused rebuild and audit. `cases.json` retains expanded input coefficients, exponents, bounds and kernel-checked point packets. `summary.json` identifies exact proof inputs, the pinned toolchain and remaining scope.

The CLI logs retain the full build-and-solve entry point, source-only cubic, exact odd-power family and a huge certificate-only bound. `cli_input_validation.json` records nine argument cases. `compatibility.log` checks equality with the previous square route; replay it with `lake env lean -s 65536 audit/RungePowerCompatibility.lean`. The Python log records 525 tests and four skips. The full historical root build and hosted runner availability are not claimed.
