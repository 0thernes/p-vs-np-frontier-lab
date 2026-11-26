<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `p-vs-np-frontier-lab` are documented in this file.
Format follows Keep a Changelog and Semantic Versioning (`VERSION`).

## [Unreleased]

## [1.2.0] - 2026-11-26

### Added
- **Concrete Non-Vacuity & Adversarial Sharpness Modules (`lean/PVsNP/NonVacuity.lean`, `lean/PVsNP/AdversarialTests.lean`):** Added 5 concrete non-vacuity witnesses (`nv_odd_cycle_k0_contextual`, `nv_mermin_peres_contextual`, `nv_witness_mat_n2`, `nv_natural_proof_n1`, `nv_catalytic_d2_concrete`) and 5 negative boundary sharpness refutations (2 strictly zero-axiom `adv_const_true_not_projection` / `adv_const_false_not_projection`, plus `adv_markov_1not_cannot_invert_2bits`, `adv_mc_and3_not_one_gate`, `adv_perm_ne_det_mod3_n2`), expanding `VerifyAxioms.lean` from 15 to **25 audited declarations** strictly within `[propext, Classical.choice, Quot.sound]`.
- **Live Negative Lean Kernel Rejection Gate (`.github/workflows/ci.yml`):** Ubuntu 6-kernel CI now compiles a temporary false claim (`permInt 2 (witnessMat 2) % 3 = detInt 2 (witnessMat 2) % 3`) and requires Lean 4.35.0 to reject it with non-zero exit code.
- **Live Crossref Citation & Retraction Auditor (`scripts/check_citations.py`, `docs/citation-audit.md`):** Independently verified **27/27** bibliography entries in `paper/main.tex` (**25 live Crossref HTTP-200 DOIs + 2 archival print records, 0 retractions**).
- **DigiCert RFC 3161 TSA Cryptographic Timestamp (`data/MANIFEST.sha256.tsr`):** Sealed `data/MANIFEST.sha256` against DigiCert's public RFC 3161 Time-Stamping Authority.
- **Interactive Searchable WCAG 2.2 AA Blueprint DAG (`scripts/build_blueprint.py`):** Added live keyword filter, SVG module click-to-highlight dependency cone, `NonVacuity` & `AdversarialTests` tables, and `prefers-reduced-motion`.
- **3-Cycle Gold-Standard Hardening Dossier (`docs/reviews/2026-11-26-3cycle-hardening-v1.2.0.md`).**

### Fixed
- **Zero Static-Analysis Warnings (`ruff=0`, `mypy=0`):** Eliminated all 14 `ruff` findings across `experiments/exp1..exp5` and `tests/test_all.py`, added `pythonpath = .` to `pytest.ini`, and fixed the 2 `mypy` variable-shadowing errors in `tests/test_all.py`.

## [1.1.0] - 2026-11-25

### Added
- **Palomar 6-Kernel Comparator Contract (`lean/PalomarChallenge.lean`, `lean/PalomarSolution.lean`, `lean/comparator.json`):** Isolated 15-target challenge/solution contract verified via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid` on Ubuntu CI across all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Build Standard v1.2.0 Full Compliance (`100.0%`):** Upgraded `repo.yaml` to Draft 2020-12 schema (`repo-standard.schema.json`), migrated to the 10-class finding taxonomy (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`), added `justfile`, `pytest.ini`, `CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`, `SUPPORT.md`, `ROADMAP.md`, `ERRATA.md`, `NOTICE`, `THIRD_PARTY_NOTICES.md`, `.gitleaks.toml`, `.github/labels.tsv`, `.github/ISSUE_TEMPLATE/`, `docs/{index,configuration,operations,faq,glossary,run-log,statement-fidelity,mega-atlas-cross-reference}.md`, `docs/reviews/2026-11-25-redteam-v1.1.0.md`, `docs/media/social-preview.svg`, and `data/MANIFEST.sha256`.
- **Interactive Proof Blueprint & Automated Live Sync:** Added `scripts/build_blueprint.py` (WCAG 2.2 AA static GitHub Pages portal), `scripts/check_readme_axioms.py`, cross-platform CI + Sigstore SLSA release workflow (`.github/workflows/release.yml`), Pages deploy workflow (`.github/workflows/pages.yml`), and real-time `repository_dispatch` notifier (`.github/workflows/notify-archive.yml`) to `0thernes/0thernes-research-archive`.
- **Expanded Verification Ladder (`tests/test_all.py`):** Added Hypothesis property-based tests (B10), mutant-killing negative tests (B06/B13), single-version consistency check (A08), Draft 2020-12 `repo.yaml` validation, R4 banned-file check, zero-unformed-LLC identity guard, and `MANIFEST.sha256` ↔ `data/MANIFEST.sha256` parity tests.

## [1.0.0] - 2026-11-23

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 13 `module` files (8,078 lines; zero `sorry`, zero custom axioms, axioms strictly within `[propext, Classical.choice, Quot.sound]`) formalizing 14 unconditional theorems (`C1`–`C14`) across Baker–Gill–Solovay dual relativization, Razborov–Rudich natural proofs, odd-cycle and Mermin–Peres maximal contextuality, Schaefer polymorphisms and all-arity inclusion-minimal rigidity of `{R000, R111}`, Markov–Fischer bounded negation, multiplicative complexity, char-2 permanent/determinant collapse, and catalytic zero-workspace multilinear algebra.
- **Multi-Kernel Verification Audit (`results/six_kernel_audit.txt`, `lean/formalization.yaml`):** All 15 exported theorems verified exit 0 across 6 kernel runs.
- **Five Computational Experiments & 15-Page AMS-LaTeX White Paper:** Frozen PDF (`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`), standalone arXiv tarball (`dist/arxiv_submission.tar.gz`), 4 vector PDF figures, and 10-pass review log.
