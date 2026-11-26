<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `p-vs-np-frontier-lab` are documented in this file.
Format follows Keep a Changelog and Semantic Versioning (`VERSION`).

## [Unreleased]

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
