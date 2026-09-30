$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
if (Get-Command py -ErrorAction SilentlyContinue) {
    & py -3 tools/verify_manifest.py
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    & py -3 tools/inspect_corpus.py
} elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
    & python3 tools/verify_manifest.py
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    & python3 tools/inspect_corpus.py
} elseif (Get-Command python -ErrorAction SilentlyContinue) {
    & python tools/verify_manifest.py
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    & python tools/inspect_corpus.py
} else {
    throw 'Install Python 3.10 or later, then rerun this script.'
}
exit $LASTEXITCODE
