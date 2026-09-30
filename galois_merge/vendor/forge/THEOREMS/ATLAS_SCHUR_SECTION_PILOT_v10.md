# v0.10 Native and ATLAS-Backed Schur-Section Library

Forge v0.10 begins populating the v16 section compiler rather than leaving `R_n(H,q)` as a schema only.

`DATA/FORMATION/native_schur_section_library_v10.json` contains 30 exact native product/diagonal-strip relations for `C4` and `C8`.  These are Atlas-independent relations valid for any chosen pairwise nonisomorphic perfect species with the stated cyclic multiplier.  They include one-species diagonal strips, two-species semisimple product targets, and three-species native unique-double sections.  The semisimple target is retained intact.

`DATA/FORMATION/atlas_schur_section_pilot_v10.json` adds three named `C2` rows for `M22`.  Standard ATLAS/GAP cover data show that relevant `A7`, `L2(11)`, and an `A5` class lift as direct products with the central involution in `2.M22`.  Thus the nontrivial `C2` cover class of `M22` restricts trivially to these sections.  In one-dimensional `C2` coordinates the rows are

`U=[0], V=[1]`, hence the relation is `0=y`: either source class is allowed, but only the trivial target extension class is compatible with that section.

This is the first named cross-species section data in Forge.  It is intentionally a pilot.  It is not an exhaustive perfect-section database and it supplies no uncomputed `C4/C8` cross-species transfer maps.
