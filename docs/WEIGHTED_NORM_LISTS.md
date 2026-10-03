# Complete nonempty norm lists and native cubic transport

`WeightedNormList.complete_of_cert` connects the existing checked norm-representative slab to a complete finite list. For each representative γ, it requires separately checked bounds M and M′ for the zero third coordinate in the forward and inverse unit orbits. The output enumerates both finite ranges and filters by the exact norm and coordinate equations. Duplicate points are permitted. `bound_of_data` supplies those bounds from the weighted Skolem theorem at an odd prime; the representative matrix need not be invertible.

The concrete certificate `WeightedNorm107` works in the order z³=−4, with η=(5,−3,2), ε=(1,−1,−1), and norm ±107. Its rational enclosure and 3,631-candidate slab are rechecked by Lean. The complete reduced representative list is [(-1,-3,0),(1,3,0)]. Both directional periods are 3, and every residue class has the required nonzero test or first-order zero test at p=3. Consequently the complete list in the original two-coordinate plane is exactly those two elements. No analytic or external orbit-generation premise is supplied by the caller.

In particular, for every pair of integers u,v,

$$u^3+4v^3=107\quad\Longleftrightarrow\quad u=-1\ \text{and}\ v=3.$$

The consumer in `parallel_formula/norm107` replaces this arithmetic atom by its finite point formula and proves the whole query with u≥0 equivalent to False. The committed solver measurements concern this single example, not the industrial portfolio or a general speedup. The original solver run has a 3-second cap; the reduced run and its exact wall time are recorded separately.

`NativeCubicNorm` proves multiplicativity of the determinant norm for the native binary-cubic multiplication table. For coefficients (a,b,c,d),

$$\operatorname{Norm}(au+v\omega)=a^2(au^3+bu^2v+cuv^2+dv^3),$$

whereas the oriented index form of ξ=uω+vθ is

$$\det[1,\xi,\xi^2]=-(au^3+bu^2v+cuv^2+dv^3).$$

The nonmonic factor a² is retained. A binary cubic's index form is not silently identified with its ring norm. `NativeCubicBridge` supplies an integral basis bridge for shifted negative-monic forms:

$$(-1,-3h,P-3h^2,Q+Ph-h^3),\qquad(x_0,x_1,x_2)\mapsto(x_0-hx_1+(h^2-P)x_2,x_1+hx_2,x_2).$$

Both inverse identities, multiplication preservation, and norm preservation are proved. Arbitrary overorders and a basis-independent nonmonic source solver remain open.

`RankOneIntegerSlab` clears a positive common denominator in a fixed rational certificate. Integer division computes the exact original floor and ceiling endpoints, and `slice_eq` proves equality with the rational slab check. The k=22 generator supports `--integer --slices 2000`, yielding 100 separately checked modules instead of the original 3,987 smaller modules. All 100 modules and the final source have now passed, followed by the complete k=22 curve theorem and the compiler consumer. Generation preserves prior check receipts only when the full source and dependency identities still match. The sequential checker additionally requires an existing Lean object when reusing a check.

Workspace maintenance removed the earlier running job and its local artifacts. The earlier report of 53 checked chunks is historical and cannot be used as a current full-source certificate. The new receipt records the completed checks in this workspace. k=22 is now in the complete registry, with exactly (3,−7) and (3,7).
