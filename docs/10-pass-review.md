<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# 10-Pass Adversarial Self-Audit & Six-Class Findings Catalog (`docs/10-pass-review.md`)

Every artifact in `p-vs-np-frontier-lab` underwent ten structured adversarial review passes before the `v1.0.0` freeze. Every discovered defect, failure mode, obstruction, or tension is classified strictly under one of six mutually exclusive labels: **`bug`**, **`error`**, **`issue`**, **`problem`**, **`dilemma`**, or **`conflict`**.

---

## Summary of All 10 Adversarial Passes

### Pass 1 — Mathematical & Logical Soundness
- Audited all 14 theorem statements (`C1`–`C14`) against textbook complexity-theoretic definitions.
- Confirmed zero circular reasoning, zero vacuous quantifiers (explicitly proved `natural_proof_nonvacuous` density $\ge 1/2$ for all $n \ge 1$ and `monotone_3sat_minimal` inclusion minimality), and explicit separation between unconditional theorems and conditional CSP reductions (`Remark 4.3`).

### Pass 2 — Lean 4.35 Statement Fidelity & Axiom Hygiene
- Inspected all 13 `.lean` files (8,078 lines; max single file 2,557 lines <= 10,000 limit; 100% `module` headers; zero Mathlib).
- Comment-stripped regex scan confirmed **0 hits** for `sorry`, `admit`, `native_decide`, `implemented_by`, custom `axiom`, or `@[extern]`.
- Caught and resolved **`bug` #1** in `RelativizationCol.lean`: `omega` rejected an initially over-tight step bound `4*c + 10` for `mulPhaseSteps 0 c <= 7*c`, prompting correction to `7*c + 10 + (colPrefBits V d).length`.
- Verified verbatim `#print axioms` (`results/lean_axioms.txt`): all 15 exported theorems stay strictly within `[propext, Classical.choice, Quot.sound]`.

### Pass 3 — Multi-Kernel Independent Replay & Clean-Room `.lake` Build
- Exported `Solution.prove_all_frontier_theorems` (31,403,462 bytes, SHA-256 `7F981919...EBB1BC764F`, 15/15 symbols present, `sorryAx=False`, `trustCompiler=False`).
- Verified exit code `0` across **6 kernel checks (5 independent implementations)**: `lean.exe`, `leanchecker.exe`, `leanchecker-paranoid.exe`, `con-leche.exe --verified` (`3982 declarations`), `con-ron.exe --verified` (`3982 declarations`), and `nanoda_bin.exe` (`4319 declarations`, `unpermitted_axiom_hard_error=true`).
- Deleted `lean/.lake` completely and verified clean-from-scratch `lake build` (16/16 jobs, 0 warnings, exit 0) + `VerifyAxioms.lean` (exit 0).
- Diagnosed and documented **`issue` #1** (upstream Windows `lean4lean.exe` rejects even stdlib `Init.Prelude.olean` with `incompatible header`; Windows `lake check` requires Linux `bwrap`/`git`).

### Pass 4 — Exact-Arithmetic & SAT Encoder Soundness
- Audited all 5 Python experiments for hidden floating-point contamination: confirmed Experiments 1, 2, 3, 4B–4D, and 5 use 100% exact integer, `fractions.Fraction`, $\mathbb{F}_2$, or CaDiCaL 2.1.2 arithmetic.
- Implemented exhaustive brute-force equivalence test in `tests/test_all.py` (`test_exp2_bruteforce_sat_encoder_equivalence_n3`) enumerating all 2,048 1-AND circuits on $n=3$ (16 affine, 128 $\mathrm{MC}\le 1$, 128 $\mathrm{MC}=2$) and verifying 100% agreement with `exp2.synthesize_mc`.
- Caught and fixed **`bug` #3** in the initial draft of `tests/test_all.py` (stale expected tuple `(4,4,1)` instead of exact `(3,3,1)` for `E_2^5`/`E_3^5`, and helper name `permanent_exact` -> `exact_perm`); all 10/10 tests now pass in 0.82 s.

### Pass 5 — Numerical Stiffness, Scaling & Adversarial Counterexamples
- Caught and fixed **`bug` #2** in `exp4` draft: replaced discontinuous `solve_ivp` event crossing with clean fixed-chunk RK45 integration + explicit discrete spin evaluation.
- Added an explicit exhaustively verified UNSAT 3-SAT arm ($n=5,10,12$) to Attack A, confirming 0/15 solved and linear $\max_m \ln a_m(t) \approx 10.68$ growth ($a_{\max} \approx 4.35\times 10^4$) vs. 20/20 solved on planted SAT; explicitly labeled `numerical_approximation` everywhere.
- Certified **`error` #1** (Attack C 3-adic Hensel root `[42,0,0,0] mod 81 -> (3/2,0,0,0)` on duplicate-free 10-clause UNSAT 3-SAT) and documented **`problem` #1** (`CLIQUE_4_3` `MC` timeout at `k=5`, honestly reported as `MC in {5,6}`).

### Pass 6 — Cross-Domain Wild-Path Gaps & Blind-Spot Audit
- Evaluated all 12 divergent pathways against the 5-barrier gauntlet (Relativization, Natural Proofs, Algebrization, Bounded Arithmetic / Meta-Complexity, Physical Energy/Precision) via deductive, inductive, and abductive inference.
- Isolated **`dilemma` #1** (Natural Proofs vs. non-natural barrier power) and **`problem` #2** ($\mathrm{P}$ vs. $\mathrm{NP}$ remains open; only Pathways 9, 10, 11 survive as active open frontiers).

### Pass 7 — Security, Supply Chain, Zero-Fabrication & Citation Audit
- Verified all 27 references in `paper/main.tex` are real, foundational publications with zero fabricated DOIs or arXiv identifiers.
- Verified zero secrets, zero credentials, zero external network calls at runtime, pinned `requirements.lock.txt` and `lean/lean-toolchain`.
- Verified **`conflict` #1** resolution (ADR 0002): author `Alexander S. Donahue` (Independent Researcher, Spokane, WA, USA; ORCID `0009-0006-8168-9648`), zero `0thernes LLC` mentions in paper/metadata, dual license `Apache-2.0` + `CC-BY-4.0`.

### Pass 8 — Visual & Typographic Polish (Figures & All 15 PDF Pages)
- Visually inspected all 4 vector PDF figures via `read_file`: caught and fixed annotation/legend overlaps on `fig1`–`fig4` across two iterations until all 4 rendered cleanly.
- Visually inspected all 15 rendered pages of `dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`: caught and fixed a severe Table 4 column-crush defect, 3 Table 2 identifier collisions, `--verified` en-dash ligatures, straight ASCII quotes, a missing space in `\code{mulPhaseSteps 0 c}`, and all Overfull/Underfull hbox warnings (final build: **0 Overfull hboxes, 0 Underfull hboxes, 0 undefined references/citations**).

### Pass 9 — Build Standard v1.1.0 & Independent Research Playbook Compliance
- Audited all required files: `VERSION`, `LICENSE`, `.gitignore`, `.gitattributes`, `.editorconfig`, `AGENTS.md`, `CLAUDE.md`, `GEMINI.md`, `.cursor/rules/build-standard.mdc`, `SECURITY.md`, `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `CHANGELOG.md`, `CITATION.cff`, `llms.txt`, `llms-full.txt`, `repo.yaml`, `MANIFEST.sha256`, `docs/plan/*`, `docs/adr/*`, `docs/architecture.md`, `docs/threat-model.md`, `docs/10-pass-review.md`, `scripts/run_all.ps1`, `.github/workflows/ci.yml`.
- Confirmed zero prohibited files (no git hooks, no Dependabot, no Copilot instructions, no branch-protection/PR workflows).
- Documented **`issue` #2** (literal brackets `[Vibe Coded (AI)]` on ReFS Dev Drive mitigated cleanly via PowerShell `-LiteralPath` and repo-relative `pytest`).

### Pass 10 — Clean-Room End-to-End Reproducibility & Provenance Freeze
- Verified standalone clean-room compilation of `dist/arxiv_submission.tar.gz` in a fresh temporary directory (exit 0).
- Verified full `scripts/run_all.ps1 -Task all` execution (exit 0), `MANIFEST.sha256` integrity check, and clean single commit straight to `main`.

---

## Consolidated Six-Class Findings Table

| # | Class | Location | Finding Summary | Resolution / Status |
|---|---|---|---|---|
| 1 | `bug` | `lean/PVsNP/RelativizationCol.lean` | Multiplication-phase step bound `4*c + 10` too tight for `mulPhaseSteps 0 c <= 7*c`; caught by `omega`. | Fixed to `7*c + 10 + (colPrefBits V d).length`; clean build exit 0. |
| 2 | `bug` | `experiments/exp4_wild_p_eq_np_falsifiers.py` | Discontinuous `solve_ivp` event crossing risked missed discrete zero crossings in early draft. | Replaced with chunked RK45 + explicit discrete spin evaluation. |
| 3 | `bug` | `tests/test_all.py` | Initial test assertions had stale `(deg, MC) = (4, 4)` for `E_2^5`/`E_3^5` (exact: `(3, 3)`) and wrong helper name `permanent_exact`. | Fixed against verified JSON & `exp5.exact_perm`; 10/10 pass. |
| 4 | `error` | `experiments/exp4_wild_p_eq_np_falsifiers.py` (Attack C) | Naive 3-adic Hensel lifting on $\sum_c P_c(x) \equiv 0 \pmod 3$ converges to non-Boolean root $(3/2, 0, 0, 0) \in \mathbb{Z}_3^4$ on UNSAT 3-SAT. | Certified mathematical falsifier (`[42,0,0,0] mod 81`). |
| 5 | `issue` | Lean 4.35.0 Windows toolchain | Bundled `lean4lean.exe` rejects stdlib `Init.Prelude.olean` (`incompatible header`); `lake check` requires Linux `bwrap`/`git`. | Documented honestly (`results/six_kernel_audit.txt`); 6/6 working kernels pass; Linux CI runs `lake check`. |
| 6 | `issue` | Windows ReFS bracketed path | Literal `[Vibe Coded (AI)]` triggers PowerShell globbing and `pytest` parametrization errors if passed unescaped. | Enforced `-LiteralPath` and repo-relative `pytest` in `scripts/run_all.ps1`. |
| 7 | `problem` | `experiments/exp2_multiplicative_complexity.py` | CaDiCaL 2.1.2 timed out at 20 s deciding `MC(CLIQUE_4_3) <= 5` ($n=6, \deg=6$). | Reported honestly as `MC in {5, 6}` (open lower bound >= 5). |
| 8 | `problem` | P vs. NP Open Frontier | All 12 pathways fail to resolve P vs. NP; only Pathways 9, 10, 11 survive the 5-barrier gauntlet as active open targets. | Explicit epistemic non-claim boundary enforced everywhere. |
| 9 | `dilemma` | Natural Proofs vs. Barrier Evasion | Large constructive properties (`deg`, `AI`, `NL`, OGP) prove restricted bounds but break PRFs (`C3`); non-natural invariants (GCT, catalytic space, magnification) resist unconditional superlinear bounds. | Central structural dilemma guiding future work. |
| 10 | `conflict` | Scholarly Identity & Licensing | Independent-research playbook flags corporate LLC affiliation and all-rights-reserved text as credibility risks for arXiv/Zenodo preprints. | Resolved in ADR 0002: independent researcher + dual `Apache-2.0` / `CC-BY-4.0`. |
