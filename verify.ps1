$ErrorActionPreference = 'Stop'
$oldThreads = $env:LEAN_NUM_THREADS
Push-Location $PSScriptRoot
try {
    $env:LEAN_NUM_THREADS = '2'
    $root = Get-Content -LiteralPath 'CauchyHorizon.lean' -Raw
    $sources = @(Get-ChildItem -LiteralPath 'CauchyHorizon' -Filter '*.lean' -Recurse)
    foreach ($source in $sources) {
        $relative = [IO.Path]::GetRelativePath($PSScriptRoot, $source.FullName)
        $module = $relative.Substring(0, $relative.Length - '.lean'.Length).Replace('\', '.').Replace('/', '.')
        if ($root -notmatch ('(?m)^import ' + [regex]::Escape($module) + '\s*$')) {
            throw "Production module is missing from the audited root: $module"
        }
        $text = Get-Content -LiteralPath $source.FullName -Raw
        if ($text -match '\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC') {
            throw "Prohibited proof placeholder or bypass in $relative"
        }
    }
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'Lean build or compiled audit failed.' }
    & lake env lean Audit.lean
    if ($LASTEXITCODE -ne 0) { throw 'Fresh axiom audit failed.' }
    Write-Host "VERIFIED productionModules=$($sources.Count)"
} finally {
    Pop-Location
    $env:LEAN_NUM_THREADS = $oldThreads
}
