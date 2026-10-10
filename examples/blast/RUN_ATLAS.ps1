$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path (Split-Path $PSScriptRoot -Parent) -Parent
$pythonCommand = Get-Command py -ErrorAction SilentlyContinue
if ($pythonCommand) {
    & $pythonCommand.Source -3 (Join-Path $repoRoot 'python/develop_blast_atlas.py')
} else {
    $pythonCommand = Get-Command python -ErrorAction Stop
    & $pythonCommand.Source (Join-Path $repoRoot 'python/develop_blast_atlas.py')
}
if ($LASTEXITCODE -ne 0) { throw 'Atlas regeneration failed; inspect the Python error above.' }
Start-Process (Join-Path $repoRoot 'web/blast-atlas/index.html')
