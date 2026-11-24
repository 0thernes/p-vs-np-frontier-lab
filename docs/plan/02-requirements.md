<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Requirements Specification (`docs/plan/02-requirements.md`)

## Functional Requirements
- **FR-1 (Epistemic Integrity):** Explicitly state that $\mathrm{P}$ vs. $\mathrm{NP}$ remains open across all documents, paper, README, and YAML ledgers; partition every claim strictly into Tiers 1–4.
- **FR-2 (Zero-Mathlib Lean 4.35 Formalization):** Formalize 14 unconditional theorems (`C1`–`C14`) across classical barriers and cross-domain phase transitions in `lean/` with zero external dependencies, `module` headers in every `.lean` file, <= 10,000 lines/file, zero `sorry`/`admit`/`native_decide`/custom `axiom`/`@[extern]`, and Challenge/Solution isolation.
- **FR-3 (Multi-Kernel Replay):** Export `Solution.prove_all_frontier_theorems` and verify across all working bundled Lean 4.35.0 external kernels (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`), documenting any upstream toolchain issues honestly.
- **FR-4 (Exact-Arithmetic & SAT Discovery/Falsification Bench):** Execute 5 reproducible Python experiments testing all 12 divergent pathways, keeping Tiers 2 (exact integer/rational/$\mathbb{F}_2$/SAT) and 3 (`numerical_approximation` float64 ODE) strictly separated.
- **FR-5 (Automated Verification & Red-Team Tests):** Provide `tests/test_all.py` verifying all experiment JSONs, negative falsification cases, Lean axiom hygiene, and a brute-force SAT-encoder equivalence check on $n=3$.
- **FR-6 (Publication-Grade Paper & Tarball):** Produce 4 vector PDF figures and a zero-overfull-hbox AMS-LaTeX white paper (`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`) plus a standalone clean-room-tested arXiv tarball (`dist/arxiv_submission.tar.gz`).
- **FR-7 (Build Standard & Provenance):** Provide `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `CITATION.cff`, `CHANGELOG.md`, `repo.yaml`, `llms.txt`, `llms-full.txt`, `MANIFEST.sha256`, `scripts/run_all.ps1`, `docs/10-pass-review.md`, and informational-only CI (`.github/workflows/ci.yml`), committing cleanly straight to `main`.

## Non-Functional Requirements
- **NFR-1 (ReFS Dev Drive & Bracket Safety):** All workspace files, `.venv`, and `.lake` caches reside under `Z:\[Vibe Coded (AI)]\ANTIGRAVITY\p-vs-np-frontier-lab`; PowerShell scripts use `-LiteralPath` everywhere.
- **NFR-2 (Identity & Licensing Compliance):** Author listed as `Alexander S. Donahue` (Independent Researcher, ORCID `0009-0006-8168-9648`, Spokane, WA, USA) with dual license `Apache-2.0` (code) + `CC-BY-4.0` (prose/figures), per ADR 0002.
- **NFR-3 (Zero Fabrication):** Zero fabricated citations, DOIs, arXiv IDs, peer-review claims, or kernel verdicts.
