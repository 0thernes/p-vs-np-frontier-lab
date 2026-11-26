<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Room Replication Guide (`REPLICATION.md`)

Every formal proof, computational experiment, test, vector figure, and frozen PDF in `p-vs-np-frontier-lab` can be independently reproduced from scratch.

## Prerequisites

- **Lean 4.35.0** via `elan` (`leanprover/lean4:v4.35.0`, pinned in `lean/lean-toolchain`). Zero Mathlib dependency.
- **Python 3.13** with pinned dependencies in `requirements.lock.txt`.
- **CaDiCaL 2.1.2** (bundled with Lean 4.35.0 at `<toolchain>/bin/cadical[.exe]`, or override via `CADICAL_BIN`).
- **Tectonic** (`tectonic -X compile`) for compiling `paper/main.tex` to PDF.

## 1. Windows PowerShell (One-Command Orchestrator)

```powershell
pwsh -File scripts/run_all.ps1 -Task all
```

## 2. Linux / macOS Step-by-Step Commands

```bash
# A. Lean 4.35 Clean Build & 6-Kernel Palomar Replay
cd lean && rm -rf .lake && lake build && lake build PalomarChallenge
lake env lean VerifyAxioms.lean
lake env leanchecker --fresh Solution
lake env leanchecker-paranoid --fresh Solution
lake check --paranoid
lake comparator --config comparator.json --paranoid

# B. Python Verification Suite, Blueprint & Checksums
cd ..
python3 -m pip install -r requirements.lock.txt
python3 -m pytest -v tests/test_all.py
python3 scripts/check_readme_axioms.py
python3 scripts/build_blueprint.py
sha256sum -c MANIFEST.sha256 && sha256sum -c data/MANIFEST.sha256

# C. Standalone arXiv Tarball Verification
mkdir -p /tmp/arxiv_check && tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_check
tectonic -X compile /tmp/arxiv_check/main.tex --outdir /tmp/arxiv_check/out
```

## Replication Log

| Date (UTC) | Replicator | Environment | Version | Outcome |
|---|---|---|---|---|
| 2026-11-23 | Alexander S. Donahue (author) | Windows 11, Lean 4.35.0, Python 3.13.12 | `1.0.0` | PASS: 16/16 Lean jobs, 6/6 kernels, 10/10 pytest, 15-page 0-overfull PDF, clean-room arXiv tarball, 18/18 SHA-256. |
| 2026-11-25 | Alexander S. Donahue + GitHub Actions CI | Windows 11 & Ubuntu/macOS/Windows hosted runners, Lean 4.35.0, Python 3.13 | `1.1.0` | PASS: 6-kernel bubblewrap `lake check --paranoid` + 15-target `lake comparator --paranoid`, expanded pytest/Hypothesis suite, Tectonic PDF/arXiv clean-room build, 100.0% Build Standard v1.2.0. |
