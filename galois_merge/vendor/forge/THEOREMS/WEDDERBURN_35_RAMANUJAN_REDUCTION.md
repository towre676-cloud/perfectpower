# 35-dimensional Ramanujan carrier reduction — v0.4

The complex Wilson Hecke algebra has simple matrix-block sizes

`1,3,3,2,5,5,5,3,3,6`,

whose squares sum to 152. Removing the trivial 1-dimensional block leaves the 151-dimensional regular augmentation representation. For a self-adjoint Wilson operator `a`, positivity of the Ramanujan slack

`Omega(a)=4(d-1)(1-e0)-(a-d e0)^2`

on that 151-dimensional regular augmentation space is equivalent to positivity on one copy of each nontrivial simple module. Those carrier dimensions are

`3,3,2,5,5,5,3,3,6`,

and sum to 35. Therefore the 151-dimensional Sylvester test is theorem-level redundant: once one irreducible carrier per simple block is known, Ramanujan status is decided by nine matrices, none larger than 6x6.

`DATA/CROSS/q192_four_channel_carriers_numeric.json` is a numerical extraction of such one-copy carriers for Q192's four unsigned channel pieces (`C3` plus three transpose-paired `C7` channels). It is obtained by first splitting the regular algebra with a generic central element and then splitting each `m^2` regular block by a commuting generic left multiplication. The maximum invariance residual is below `5e-13`. Summing the four extracted carrier matrices reproduces Q192's nontrivial spectral radius `38.478919032...`, including the known extremal 5-dimensional block.

The **35-dimensional reduction itself is exact representation theory**. The frozen carrier coordinates are numerical and are therefore a fast search/evaluation dictionary, not a replacement for the exact 151-dimensional positivity certificates. An exact algebraic carrier dictionary remains a downstream arithmetic task.
