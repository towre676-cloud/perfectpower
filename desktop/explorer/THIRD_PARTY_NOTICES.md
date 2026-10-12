# PerfectPower Explorer third-party components

The desktop shell uses Electron 44.7.0, whose MIT license and bundled Chromium notices are retained in the portable application. Source and releases: https://github.com/electron/electron . The Python runtime is the official CPython 3.12.10 Windows x64 embeddable distribution; its license is included. Source: https://www.python.org/downloads/release/python-31210/ . Runtime acquisition hashes are recorded in RUNTIME_SOURCES.json.

The interface bundles Three.js 0.186.1 (MIT), Lucide 0.577.0 (ISC), Marked 16.4.2 (MIT), and DOMPurify 3.3.1 (Apache-2.0 OR MPL-2.0). The build retains their bundled license comments and package-lock dependency records. Source projects are https://github.com/mrdoob/three.js , https://github.com/lucide-icons/lucide , https://github.com/markedjs/marked , and https://github.com/cure53/DOMPurify . Esbuild and Playwright are development tools.

The studio lighting asset is Poly Haven's studio_small_09 1K HDR environment, distributed under CC0. Source: https://polyhaven.com/a/studio_small_09 . Download: https://dl.polyhaven.org/file/ph-assets/HDRIs/hdr/1k/studio_small_09_1k.hdr . The asset is bundled locally; no remote asset request is necessary at runtime. The PerfectPower symbol and interface layout were created for this application.

The numerical Python libraries are numpy 2.2.6, scipy 1.15.3, sympy 1.14.0, mpmath 1.3.0, python-flint 0.9.0, and z3-solver 5.1.0.0. Their wheel-provided metadata and license files accompany the unpacked runtime. Their source repositories and original wheel hashes are preserved in the runtime record. These libraries provide their own native dependencies within the wheels.

The native planner and CNF counter are built from PerfectPower's included C++ source. Windows builds use MinGW GCC 13-posix with static libgcc/libstdc++; libwinpthread-1.dll is included beside the counters. GCC runtime components are distributed under their upstream licenses and GCC Runtime Library Exception; MinGW-w64 runtime notices accompany the source-build instructions. The upstream source is available from https://www.mingw-w64.org/ and https://gcc.gnu.org/ . The project-native arithmetic sources retain PerfectPower's Apache-2.0 license.

Every pre-existing repository asset retains its original notice and attribution. The complete checkout includes LICENSE, LICENSE-docs, and dataset-specific source documents. Packaging does not relicense OEIS records, biological data, retained images, or other third-party material.
