<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Verification & Audit Run Log (`docs/run-log.md`)

| Date (UTC) | Version | Operator / Runner | Command | Outcome |
|---|---|---|---|---|
| 2026-11-23 | `1.0.0` | Alexander S. Donahue (Win11, Lean 4.35.0, Python 3.13) | `pwsh -File scripts/run_all.ps1 -Task all` | PASS: 16/16 Lean jobs, 6/6 working kernels, 10/10 pytest, 15-page 0-overfull PDF, clean-room arXiv tarball, 18/18 SHA-256. |
| 2026-11-25 | `1.1.0` | Alexander S. Donahue + AI audit (Win11 + Ubuntu CI) | `lake build`, `pytest`, `check_readme_axioms.py`, `build_blueprint.py`, `Audit-Repo.ps1` | PASS: Palomar 15-target `comparator.json` added, Build Standard v1.2.0 upgraded (`48.0% -> 100.0%`), public GitHub release & archive registration `0TH-2026-013`. |
