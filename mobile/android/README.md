# PerfectPower Explorer Android

A complete offline repository explorer with embedded Python engines, touch-first navigation, a 3D equation laboratory, exact command forms, editable inputs, proof browsing, saved runs and Android file export. Android 13 or newer; ARM64 phones and x86-64 emulator support.

`COVERAGE.md` records runtime boundaries. `CONTENT_CHECKS.json` verifies every original repository file. `COMMAND_COVERAGE.json` lists all 145 forms; 143 command-family help routes passed, while the two server entries use the built-in visual service. These help checks are not mathematical verification of every possible operation.

Build prerequisites: Java 17, Gradle 8.11.1, Android SDK platform 35 and Build Tools 35.0.0, Python 3.10 for Chaquopy requirements. `PP_BUILD_PYTHON` selects that interpreter. Set `ANDROID_HOME` or local `local.properties`. The Gradle configuration downloads Chaquopy 17.0.0, Android Gradle Plugin 8.9.2 and pinned Android Python wheels.

The accompanying repository archive is the full snapshot, not a scaffold. `app/src/main/assets/repository.zip` contains the actual engine source, documentation, Lean proof files, data, examples, original desktop source and native libraries. `original-files.json` and `repository.sha256` drive first-launch verification. `package_assets.py` reproduces this bundle from the complete desktop ZIP and the generated mobile interface; adjust its RELEASE path when using a different checkout location.

The UI build is `npm ci --ignore-scripts` then `npm run build` in `ui/`. `mobile.css` supplies the phone layout and `mobile-ui.js` the full-workspace menu. The repository source stays byte-identical; only its generated explorer distribution is adapted. NDK r27d builds `completion_planner.cpp` and `native/model_counting/counter.cpp` for ARM64 and x86-64 with `-std=c++17 -O3 -fPIC -shared -static-libstdc++ -Wl,-z,max-page-size=16384`; the counter additionally uses Boost 1.86.0 headers. Source and binary hashes travel in the native receipts.

Build the APK with `gradle assembleRelease`; align and sign using Android SDK `zipalign` and `apksigner`. The release signing key is stored separately from public source and downloads. Keep the private update key to sign later upgrades of this application ID. The application requests internet permission for its loopback API and optional original network adapters, and no broad storage permission. Its compute service is private and unexported.

The Android instrumentation check is `gradle connectedDebugAndroidTest` with an Android device or emulator. It checks all navigation, file and command counts, exact arithmetic, C++ counting, multiple workbenches and cancellation recovery through the real WebView and Android compute service. UI preview limits do not truncate exported stdout or generated files.
