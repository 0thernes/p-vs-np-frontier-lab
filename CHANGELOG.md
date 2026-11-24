<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `p-vs-np-frontier-lab` are documented in this file.
Format follows Keep a Changelog and Semantic Versioning (`VERSION`).

## [1.0.0] - 2026-11-23

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 13 `module` files (8,078 lines; zero `sorry`, zero custom axioms, axioms strictly within `[propext, Classical.choice, Quot.sound]`) formalizing 14 unconditional theorems (`C1`–`C14`) across Baker–Gill–Solovay dual relativization (`PVsNP.OTM`, `RelativizationSep`, `RelativizationCol`), exact-integer Razborov–Rudich natural proofs (`PVsNP.NaturalProofs`), odd-cycle and Mermin–Peres maximal contextuality + Schaefer polymorphisms + all-arity inclusion-minimal rigidity of `{R000, R111}` (`PVsNP.SheafPolymorphism`), Markov–Fischer bounded negation + multiplicative complexity degree lower bound + characteristic-2 permanent/determinant collapse and universal $p \ge 3$ witness $W_n$ (`PVsNP.CircuitPhaseTransition`), and Landauer-reversible zero-workspace $d$-fold catalytic multilinear multiplication in $3\cdot 4^{d-1}$ operations (`PVsNP.CatalyticAlgebra`).
- **Multi-Kernel Verification Audit (`results/six_kernel_audit.txt`, `lean/formalization.yaml`):** All 15 exported theorems verified exit 0 across 6 kernel runs (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) with transparent diagnosis of upstream Windows `lean4lean.exe` header mismatch and `lake check` sandbox limitation.
- **Five Computational Experiments (`experiments/`):** Exact polymorphism/Tseitin contextuality census (`exp1`), CaDiCaL 2.1.2 exact multiplicative complexity synthesis (`exp2`), exhaustive Markov inverter + Berkowitz slice + catalytic scaling (`exp3`), adversarial falsification of four wild $\mathrm{P}=\mathrm{NP}$ attacks (`exp4`, explicitly tagging Attack A RK45 ODE as `numerical_approximation` with planted SAT vs. exhaustively UNSAT arms), and char-2 collapse + exact rational Mignon–Ressayre Hessian ranks (`exp5`).
- **Automated Verification Suite (`tests/test_all.py`):** 10 tests including an exhaustive brute-force SAT-encoder equivalence audit on $n=3$ and negative falsification checks.
- **Publication-Grade AMS-LaTeX White Paper & Figures (`paper/`, `dist/`):** 4 colorblind-safe vector PDF figures, zero-overfull-hbox 15-page frozen PDF (`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`), and clean-room-tested standalone arXiv tarball (`dist/arxiv_submission.tar.gz`).
- **Governance, Audit & Provenance Artifacts:** `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `CITATION.cff`, `repo.yaml`, `llms.txt`, `llms-full.txt`, `MANIFEST.sha256`, `docs/10-pass-review.md`, `scripts/run_all.ps1`, and informational-only Linux CI (`.github/workflows/ci.yml`).
