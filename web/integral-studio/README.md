# PerfectPower · The Resonance Field

The default opening is a full-screen autonomous React Three Fiber composition. Five luminous structures present the actual 384 primitive conductor-1680 phases, their 8-fold phase image with multiplicity 48, the 264 lifted branches, the 240 E₈ roots and their true adjacency graph, and the exact integral-energy surface. Four camera sequences unfold with large mathematical overlays. Bloom, translucent surfaces, moving power-map tracers and spatial choreography supply the visual presentation. The calculation studio is reached through Explore or `?study=1`.

The retained study workspace is a self-contained React Three Fiber studio for the four-mode spectral integral. The four views display its actual density, E₈ root projection and primitive eigenphases, exact Fourier coefficients, and fixed-d Gram-energy slices. The guided tour, manual controls, shared mixture links, independent quadrature, local study checkpoints, JSON and PNG exports, and an offline HTML edition use the same mathematical engine.

The published entry is https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/ . The preceding resonance visualization remains at `/integrals/resonance.html`.

From this directory, install the pinned dependencies with `pnpm install --frozen-lockfile`, run `pnpm test`, then `pnpm build`. `node verify-ui.mjs` checks React server rendering and the typesetting of all displayed mathematics. A browser interaction check is separate from these checks. `STUDIO_DEPENDENCY_PATHS` may point to a directory containing a compatible installed `node_modules` tree when building in a managed workspace.

`math-engine.mjs` contains exact formula metadata and binary64 evaluation. Independent quadrature splits the interval at its four logarithmic singularities and flattens panel endpoints. `studio-geometry.mjs` derives each displayed surface from those formulas. `mathematics.json` and `build-receipt.json` retain the mathematical checks and source hashes. The two mathematical accounts are `docs/INTEGRAL_STUDIO_MATHEMATICS.md` and `docs/INTEGRAL_STUDIO_MONOGRAPH.md`.

`build-studio.mjs` writes the public assets into `../integral-families` and the complete offline studio into the task output folder. Its embedded math fonts and JavaScript require no CDN. Publishing regenerates the dedicated mathematics feed with `PYTHONPATH=python python python/export_integral_atlas.py`; it does not require publishing unrelated application feeds.

The analytic identities have written classical proofs. The inherited 102 Lean theorems support the finite lattice, phase-filter and induction bridge; no new Lean verification is claimed for the analytic identities or renderer. The root cloud is an explicitly described projection, and the golden character colors belong to eigenphases, not individual E₈ roots. The 3D energy scene is a slice of a four-dimensional quadratic form, centered at the slice minimum and scaled by basis norms.
