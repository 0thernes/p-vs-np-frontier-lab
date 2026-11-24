# AGENTS.md — Canonical Agent & Maintainer Entry Point

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

- **Project:** `p-vs-np-frontier-lab` — Anatomy of the P versus NP Barrier Wall: Six-Kernel Lean 4.35.0 Formalization, Exact Computational Falsification Suite, and Adversarial Audit of Unconventional Approaches
- **Author:** Alexander S. Donahue (independent researcher), ORCID `0009-0006-8168-9648`, Spokane, WA, USA (`0_0@0thernes.art`)
- **Current Build Pipeline Phase:** `P6–P7` (Build & Verify; P0–P5 completed and documented in `docs/plan/` and `docs/adr/`)
- **Target Profile:** Research Formalization + Exact Computational Verification Lab (zero-Mathlib Lean 4.35.0 + Python 3.13 + CaDiCaL 2.1.2 + Tectonic AMS-LaTeX)
- **Epistemic Status of P vs NP:** **COMPLETELY OPEN.** This repository proves **neither** `P = NP` **nor** `P ≠ NP`. Every claim is tagged in `CLAIMS.md` as `kernel-checked`, `certificate-checked`, `exact-computation`, `numerical-approximation`, `paper-proof`, or `open-conjecture`.

## Non-Negotiable Rules

1. **Zero fabrication & zero overclaiming:** Never claim to have proved `P = NP` or `P ≠ NP`, never invent numbers, DOIs, or citations, and never claim a check passed without running it in the current tree.
2. **Formal verification hygiene:** Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`, zero `implemented_by` or `@[extern]`. Every headline theorem in `lean/Challenge.lean` and `lean/Solution.lean` must report `#print axioms` strictly within `[propext, Classical.choice, Quot.sound]` and pass replay through Lean 4.35.0 (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) and `lake comparator`.
3. **PowerShell bracket-safety (Windows `Z:\[Vibe Coded (AI)]`):** Always pass `-LiteralPath` to PowerShell file cmdlets.
4. **Finding classification:** Classify every finding as exactly one of: `bug`, `error`, `issue`, `problem`, `dilemma`, `conflict`.
5. **Commit workflow:** Small, reversible commits straight to `main`; informational CI only (no blocking gates, no PR templates, no Dependabot, no `.github/copilot-instructions.md`).
6. **Legal & entity accuracy:** Use `Alexander S. Donahue (independent researcher)` — do not assert an unformed LLC as author, affiliation, or copyright holder (see `docs/adr/0002-epistemic-scope-and-identity.md`).

## One-Command Verification (`scripts/run_all.ps1` / `scripts/run_all.sh`)

- `pwsh -File scripts/run_all.ps1 -Task test` — run full Python exact-computation and falsification test suite (`pytest`)
- `pwsh -File scripts/run_all.ps1 -Task lean` — clean Lean 4.35.0 build + forbidden-token audit + `#print axioms` + 6-kernel verification + `lake comparator`
- `pwsh -File scripts/run_all.ps1 -Task experiments` — regenerate all exact computational experiments (`results/*.json`) and publication vector figures (`paper/figures/*.pdf`)
- `pwsh -File scripts/run_all.ps1 -Task paper` — compile AMS-LaTeX white paper (`paper/main.tex` → `dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`) and arXiv tarball
- `pwsh -File scripts/run_all.ps1 -Task all` — run everything end-to-end and verify `MANIFEST.sha256`

## Reference Standards

- Defensible Independent AI Research Playbook (`I:\White Papers\DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md`)
- Build Standard for LLMs v1.1.0 (`I:\All GH Repos\Repo Checklist\build-standard\build-standard.md`)
- Build Pipeline Models v1.0.0 (`I:\All GH Repos\Build Pipeline Models\build-pipeline-models\checklist.md`)
- Unsolved Mathematics Atlas P vs NP dossier (`Z:\[Vibe Coded (AI)]\CLAUDECODE\Unresolved Math Problems\problems\p-versus-np\`)
