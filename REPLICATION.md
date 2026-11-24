<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Room Replication Guide (`REPLICATION.md`)

Every formal proof, computational experiment, test, vector figure, and frozen PDF in `p-vs-np-frontier-lab` can be independently reproduced from scratch.

## Prerequisites

- **Lean 4.35.0** via `elan` (`leanprover/lean4:v4.35.0`, pinned in `lean/lean-toolchain`). Zero Mathlib dependency; builds offline once the Lean 4.35.0 toolchain is installed.
- **Python 3.13** with pinned dependencies in `requirements.lock.txt` (`numpy==2.5.5`, `scipy==1.18.1`, `matplotlib==3.11.2`, `pytest==9.2.0`).
- **CaDiCaL 2.1.2** (bundled with Lean 4.35.0 at `<toolchain>/bin/cadical[.exe]`, or override via `CADICAL_BIN` environment variable).
- **Tectonic** (`tectonic -X compile`) for compiling `paper/main.tex` to PDF.

## 1. Windows PowerShell (One-Command Orchestrator)

> **Path Safety Note:** If cloning under a directory containing `[...]` characters, always pass `-LiteralPath` to PowerShell file cmdlets and invoke `pytest` relative to the repository root.

```powershell
# Run the full pipeline (Lean build + axioms + pytest + figures + PDF + SHA-256)
pwsh -File scripts/run_all.ps1 -Task all

# Or run individual stages:
pwsh -File scripts/run_all.ps1 -Task lean
pwsh -File scripts/run_all.ps1 -Task experiments
pwsh -File scripts/run_all.ps1 -Task tests
pwsh -File scripts/run_all.ps1 -Task figures
pwsh -File scripts/run_all.ps1 -Task paper
pwsh -File scripts/run_all.ps1 -Task audit
```

## 2. Linux / macOS Step-by-Step Commands

### A. Lean 4.35 Clean Build & Multi-Kernel Replay

```bash
cd lean
rm -rf .lake
lake build
lake env lean VerifyAxioms.lean

# External replay checkers bundled with Lean 4.35.0
lake env leanchecker Solution
lake env leanchecker-paranoid Solution

# Export self-contained NDJSON stream for verified external kernels
lake env leanexport Solution -- Solution.prove_all_frontier_theorems > /tmp/solution_export.ndjson
con-leche --verified /tmp/solution_export.ndjson
con-ron --verified /tmp/solution_export.ndjson

# On Linux with bwrap + git:
lake check --paranoid
```

### B. Python Exact-Arithmetic Experiments & Pytest Suite

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.lock.txt

python experiments/exp1_polymorphism_census.py
python experiments/exp2_multiplicative_complexity.py
python experiments/exp3_markov_and_catalytic.py
python experiments/exp4_wild_p_eq_np_falsifiers.py
python experiments/exp5_char2_permanent_determinant.py

pytest -v tests/test_all.py
```

### C. Vector Figures & AMS-LaTeX White Paper

```bash
python scripts/make_figures.py
cd paper
mkdir -p build
tectonic -X compile main.tex --outdir build --keep-intermediates
```

### D. Standalone arXiv Tarball Verification

```bash
mkdir -p /tmp/arxiv_check
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_check
cd /tmp/arxiv_check
tectonic -X compile main.tex --outdir out
```

### E. Cryptographic Provenance Check (`MANIFEST.sha256`)

```bash
sha256sum -c MANIFEST.sha256
```
