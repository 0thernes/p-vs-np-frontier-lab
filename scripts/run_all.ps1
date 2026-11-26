# SPDX-License-Identifier: Apache-2.0
<#
.SYNOPSIS
  End-to-end reproducible verification orchestrator for p-vs-np-frontier-lab.
.PARAMETER Task
  One of: all, lean, experiments, tests, figures, paper, audit.
#>
param(
    [ValidateSet("all", "lean", "experiments", "tests", "figures", "paper", "audit")]
    [string]$Task = "all"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$Repo = Split-Path -Parent $PSScriptRoot
$Py   = Join-Path $Repo ".venv\Scripts\python.exe"
$Pytest = Join-Path $Repo ".venv\Scripts\pytest.exe"
$Tectonic = Join-Path $env:USERPROFILE ".local\bin\tectonic.exe"
$ElanBin  = Join-Path $env:USERPROFILE ".elan\bin"
$LeanBin  = Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---v4.35.0\bin"

if (Test-Path -LiteralPath $ElanBin) {
    $env:PATH = "$ElanBin;$LeanBin;$env:PATH"
}

function Run-Step([string]$Label, [scriptblock]$Body) {
    Write-Host "`n=== [$Label] ===" -ForegroundColor Cyan
    & $Body
    if ($LASTEXITCODE -ne 0) {
        throw "Step '$Label' failed with exit code $LASTEXITCODE"
    }
}

function Invoke-Lean {
    Run-Step "Lean 4.35 lake build + VerifyAxioms + leanchecker-paranoid" {
        Push-Location -LiteralPath (Join-Path $Repo "lean")
        try {
            & lake build
            if ($LASTEXITCODE -ne 0) { return }
            & lake env lean VerifyAxioms.lean
            if ($LASTEXITCODE -ne 0) { return }
            & lake env leanchecker Solution
            if ($LASTEXITCODE -ne 0) { return }
            & lake env leanchecker-paranoid Solution
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Experiments {
    $scripts = @(
        "experiments/exp1_polymorphism_census.py",
        "experiments/exp2_multiplicative_complexity.py",
        "experiments/exp3_markov_and_catalytic.py",
        "experiments/exp4_wild_p_eq_np_falsifiers.py",
        "experiments/exp5_char2_permanent_determinant.py"
    )
    Push-Location -LiteralPath $Repo
    try {
        foreach ($s in $scripts) {
            Run-Step "Experiment $s" { & $Py $s }
        }
    } finally {
        Pop-Location
    }
}

function Invoke-Tests {
    Run-Step "Pytest verification suite (repo-relative for bracket safety)" {
        Push-Location -LiteralPath $Repo
        try {
            & $Pytest -v tests/test_all.py
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Figures {
    Run-Step "Generate 4 vector PDF figures" {
        Push-Location -LiteralPath $Repo
        try {
            & $Py scripts/make_figures.py
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Paper {
    Run-Step "Compile AMS-LaTeX white paper with Tectonic" {
        $paperDir = Join-Path $Repo "paper"
        $buildDir = Join-Path $paperDir "build"
        if (-not (Test-Path -LiteralPath $buildDir)) {
            New-Item -ItemType Directory -Path $buildDir -Force | Out-Null
        }
        Push-Location -LiteralPath $paperDir
        try {
            & $Tectonic -X compile main.tex --outdir build --keep-intermediates
        } finally {
            Pop-Location
        }
    }
}

function Invoke-Audit {
    Run-Step "Verify SHA-256 provenance manifest (MANIFEST.sha256)" {
        Push-Location -LiteralPath $Repo
        try {
            & $Py -c @"
import hashlib, pathlib, sys
manifest = pathlib.Path('MANIFEST.sha256')
if not manifest.exists():
    print('MISSING MANIFEST.sha256', file=sys.stderr)
    sys.exit(1)
ok = 0
for raw in manifest.read_text(encoding='utf-8').splitlines():
    line = raw.strip()
    if not line or line.startswith('#'):
        continue
    expected, rel = line.split('  ', 1)
    p = pathlib.Path(rel)
    if not p.exists():
        print(f'MISSING FILE: {rel}', file=sys.stderr)
        sys.exit(1)
    actual = hashlib.sha256(p.read_bytes()).hexdigest().lower()
    if actual != expected.lower():
        print(f'SHA256 MISMATCH: {rel} expected={expected} actual={actual}', file=sys.stderr)
        sys.exit(1)
    ok += 1
print(f'MANIFEST_SHA256_VERIFIED: {ok}/{ok} files match exact checksums.')
"@
        } finally {
            Pop-Location
        }
    }
}

switch ($Task) {
    "lean"        { Invoke-Lean }
    "experiments" { Invoke-Experiments }
    "tests"       { Invoke-Tests }
    "figures"     { Invoke-Figures }
    "paper"       { Invoke-Paper }
    "audit"       { Invoke-Audit }
    "all"         {
        Invoke-Lean
        Invoke-Tests
        Invoke-Figures
        Invoke-Paper
        Invoke-Audit
    }
}

Write-Host "`nALL REQUESTED TASKS COMPLETED SUCCESSFULLY ($Task)." -ForegroundColor Green
