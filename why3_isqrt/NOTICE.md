# Source attribution and licensing

The supplied PerfectPower snapshot is the author's repository at commit `63787ac700521dda01e1a34b6fcf69c89e4188cb`, branch `claude/laughing-lamport-qqzdo9`. Its own license and notices govern that snapshot. The overlay is proposed work, not a published upstream release.

The Why3 examples are independently authored. Their original files and license are retained in `upstream/hipsleek__why3`. They were obtained at commit `ea0810ea51a237280dcd800490b5dcebb6bc3d9e`. The Von Neumann example credits Claude Marché and Sylvain Dailler. Why3's license is LGPL 2.1 with its stated exception. The exported SMT files are derived from those examples. They are fixtures, not original PerfectPower programs.

The AdaCore regression files are retained under `upstream/AdaCore__spark2014`, at commit `627d89b487155aa5f925a96e4492931047ca0f8b`. The repository's LICENSE is included. These are inspected reference programs; this handoff does not claim a GNATprove execution or a fix to their recorded warnings.

Mark Dickinson's independently authored CPython integer-square-root proof is retained under `upstream/mdickinson__snippets`, at commit `41ce2d256fef06fb32f24fe7014cfa95173ac5e0`, with its LICENSE. `ArithmeticWorkflow.lean` adapts the mathematical scaled-Newton statement to Lean 4.20 and gives new proof scripts. The source is credited in the module and monograph. This is not a proof of the CPython executable.

Runtime binaries, Mathlib caches, proprietary software, credentials and Git metadata are excluded. Lean and Why3 are installed separately under their own licenses. `runtime/proc_self_compat.c` is an optional environment-specific loader shim, not a modified Lean kernel. Ordinary installations do not need it.
