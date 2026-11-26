<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# P vs. NP Frontier & Barrier Anatomy Lab (`p-vs-np-frontier-lab`)

[![CI](https://github.com/0thernes/p-vs-np-frontier-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/p-vs-np-frontier-lab/actions/workflows/ci.yml)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-A6CE39.svg)](https://orcid.org/0009-0006-8168-9648)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0_%7C_6_Kernels-2ea44f.svg)](lean/Challenge.lean)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/License-Apache--2.0_%2F_CC--BY--4.0-blue.svg)](LICENSE)
[![Project Status: Active](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)

A zero-Mathlib Lean 4.35.0 formalization, exact-arithmetic/SAT falsification laboratory, and 15-page AMS-LaTeX preprint auditing classical complexity-theoretic barriers and twelve divergent pathways toward $\mathrm{P}$ vs. $\mathrm{NP}$.

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID: [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648))  
**Version:** `1.2.0` · **Archive Entry:** `0TH-2026-013` in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) · **Blueprint:** [Interactive Proof Blueprint](https://0thernes.github.io/p-vs-np-frontier-lab/) · **Citations:** [27/27 Live Crossref Verified (0 Retractions)](docs/citation-audit.md)

> ### Epistemic Scope Boundary (Explicit Non-Claim)
> **$\mathrm{P}$ vs. $\mathrm{NP}$ remains completely open.** Nothing in this repository claims a proof of $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$.  
> This repository delivers:
> 1. **Tier 1 (Machine-Checked Lean 4.35 Theorems `C1`–`C14` + 5 `NonVacuity` + 5 `AdversarialTests` = 25 Audited Declarations):** 14 unconditional complexity-barrier, algebraic-rigidity, circuit phase-transition, and zero-workspace catalytic theorems plus 5 concrete non-vacuity witnesses and 5 negative sharpness refutations (zero Mathlib, `module` headers, `autoImplicit = false`) verified across **all 6 independent kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) via `lake check --paranoid`, `lake comparator --config comparator.json --paranoid`, and a **live negative Lean kernel rejection check** in CI with zero `sorry`s in all proof modules and zero custom axioms.
> 2. **Tier 2 (Exact-Arithmetic & SAT-Certified Experiments):** 4 exact integer/rational/$\mathbb{F}_2$/CaDiCaL 2.1.2 computational experiments + automated `pytest` verification suite (including an exhaustive brute-force SAT-encoder audit on $n=3$, Hypothesis property tests, and negative/mutant checks).
> 3. **Tier 3 (Explicitly Tagged `numerical_approximation`):** Adaptive `float64` RK45 ODE benchmark for Attack A (CTDS) contrasting planted SAT convergence against exact UNSAT exponential Lagrange energy blowup.
> 4. **Tier 4 (Publication-Grade AMS-LaTeX White Paper):** 15-page frozen PDF ([`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`](dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf)) and clean-room-tested arXiv source tarball ([`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)).

---

## 5-Second Verbatim Axiom & Kernel Proof Check

Verify every single theorem in `lean/Solution.lean` from scratch (requires Lean `v4.35.0`, zero Mathlib download):

```bash
cd lean
lake build
lake env lean VerifyAxioms.lean
# On Linux with bubblewrap (also run automatically in GitHub Actions CI):
lake build PalomarChallenge
lake check --paranoid
lake comparator --config comparator.json --paranoid
```

**Verbatim output (`results/lean_axioms.txt` — all 25 audited declarations):**

```text
'Solution.prove_p_subset_np' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_natural_proof_breaks_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_hybrid_telescoping' depends on axioms: [propext, Quot.sound]
'Solution.prove_natural_proof_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_odd_cycle_contextual' depends on axioms: [propext, Quot.sound]
'Solution.prove_mermin_peres_contextual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_tractable_polymorphisms' depends on axioms: [propext]
'Solution.prove_monotone_3sat_rigid' depends on axioms: [propext, Quot.sound]
'Solution.prove_markov_inverter_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_fischer_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_multiplicative_complexity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_perm_det_char2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_catalytic_algebra' depends on axioms: [propext, Quot.sound]
'Solution.prove_all_frontier_theorems' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.NonVacuity.nv_odd_cycle_k0_contextual' depends on axioms: [propext, Quot.sound]
'PVsNP.NonVacuity.nv_mermin_peres_contextual' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.NonVacuity.nv_witness_mat_n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.NonVacuity.nv_natural_proof_n1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.NonVacuity.nv_catalytic_d2_concrete' depends on axioms: [propext, Quot.sound]
'PVsNP.AdversarialTests.adv_const_true_not_projection' does not depend on any axioms
'PVsNP.AdversarialTests.adv_const_false_not_projection' does not depend on any axioms
'PVsNP.AdversarialTests.adv_markov_1not_cannot_invert_2bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.AdversarialTests.adv_mc_and3_not_one_gate' depends on axioms: [propext, Classical.choice, Quot.sound]
'PVsNP.AdversarialTests.adv_perm_ne_det_mod3_n2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Multi-Kernel Verification Ledger (`results/six_kernel_audit.txt`)

| Checker / Kernel | Independent Implementation | Exit | Verdict |
|---|---|---|---|
| `lean` + `VerifyAxioms.lean` | C++ reference kernel | `0` | 0 warnings, strictly `[propext, Classical.choice, Quot.sound]` |
| `leanchecker Solution` | C++ external `.olean` replay | `0` | Accepted full import closure |
| `leanchecker-paranoid Solution` | C++ paranoid `.olean` replay | `0` | Full paranoid definitional checks passed |
| `lean4lean` (Ubuntu CI) | Verified Lean-in-Lean kernel (`lake check --paranoid`) | `0` | Accepted via bubblewrap CI replay |
| `con-leche --verified` | Verified Lean-in-Lean set-model kernel | `0` | `accepted 3982 declarations (--verified)` |
| `con-ron --verified` | Aeneas-verified Rust arena kernel | `0` | `accepted 3982 declarations (--verified)` |
| `nanoda_bin` 0.4.19 | Independent Rust external typechecker | `0` | `Checked 4319 declarations`, 0 errors (`unpermitted_axiom_hard_error=true`) |

---

## Statement-Fidelity Table (`lean/Challenge.lean` ↔ `lean/Solution.lean`)

Full line-by-line literature mapping: [`docs/statement-fidelity.md`](docs/statement-fidelity.md) · Mega-Atlas V2 cross-check (`0 / 1,900` grand problems retired): [`docs/mega-atlas-cross-reference.md`](docs/mega-atlas-cross-reference.md).

| ID | Lean Module | Challenge Statement / Solution Proof | Mathematical Result |
|---|---|---|---|
| `C1` | `PVsNP.OTM` | `PSubsetNPStmt` / `prove_p_subset_np` | $\forall O,\; \mathrm{P}^O \subseteq \mathrm{NP}^O$ (explicit 4-tape OTM) |
| `C2` | `PVsNP.Relativization` | `BakerGillSolovayStmt` / `prove_baker_gill_solovay` | $\exists A,B,\; \mathrm{P}^A = \mathrm{NP}^A \land \mathrm{P}^B \neq \mathrm{NP}^B$ |
| `C3` | `PVsNP.NaturalProofs` | `NaturalProofBreaksPRFStmt` / `prove_natural_proof_breaks_prf` | Exact cross-multiplied $\mathbb{Z}$ Razborov–Rudich PRF break |
| `C4` | `PVsNP.NaturalProofs` | `HybridTelescopingStmt` / `prove_hybrid_telescoping` | Exact $\mathbb{Z}$ hybrid telescoping triangle inequality |
| `C5` | `PVsNP.NaturalProofs` | `NaturalProofNonVacuousStmt` / `prove_natural_proof_nonvacuous` | `nonConstantProp` density $\ge 1/2$ for all $n \ge 1$ |
| `C6` | `PVsNP.SheafPolymorphism` | `OddCycleContextualStmt` / `prove_odd_cycle_contextual` | Odd cycles $C_{2k+3}$ maximally contextual for all $k$ |
| `C7` | `PVsNP.SheafPolymorphism` | `MerminPeresContextualStmt` / `prove_mermin_peres_contextual` | Mermin–Peres $3\times 3$ magic square maximally contextual |
| `C8` | `PVsNP.SheafPolymorphism` | `TractablePolymorphismsStmt` / `prove_tractable_polymorphisms` | Maltsev XOR, Horn AND, Dual-Horn OR, 2-SAT Majority |
| `C9` | `PVsNP.SheafPolymorphism` | `Monotone3SATRigidStmt` / `prove_monotone_3sat_rigid` | $\forall k \ge 1$, $\{R_{000}, R_{111}\}$ inclusion-minimal rigid |
| `C10` | `PVsNP.CircuitPhaseTransition` | `MarkovInverterTightStmt` / `prove_markov_inverter_tight` | $k$ NOT gates invert $n$ bits $\iff n \le 2^k - 1$ |
| `C11` | `PVsNP.CircuitPhaseTransition` | `FischerReductionStmt` / `prove_fischer_reduction` | Universal dual-rail compilation to $\le k$ NOT gates |
| `C12` | `PVsNP.CircuitPhaseTransition` | `MultiplicativeComplexityStmt` / `prove_multiplicative_complexity` | $\deg_{\mathbb{F}_2}(f) \le k + 1$ and $\mathrm{MC}(\mathrm{AND}_n) \ge n - 1$ |
| `C13` | `PVsNP.CircuitPhaseTransition` | `PermDetChar2Stmt` / `prove_perm_det_char2` | $\mathrm{Perm}_n \equiv \det_n \pmod 2$ and $W_n$ separating mod all $p \ge 3$ |
| `C14` | `PVsNP.CatalyticAlgebra` | `CatalyticAlgebraStmt` / `prove_catalytic_algebra` | Bijective reversibility & exact $3\cdot 4^{d-1}$ $d$-fold zero-workspace mul |

---

## Quickstart & Usage

```bash
git clone https://github.com/0thernes/p-vs-np-frontier-lab.git
cd p-vs-np-frontier-lab
python3 -m pip install -r requirements.lock.txt

# One-word recipes (justfile)
just test        # Exact arithmetic, brute-force SAT encoder audit, Hypothesis & negative tests
just axioms      # Verify verbatim #print axioms parity against results/lean_axioms.txt
just lean        # Clean Lean 4.35.0 build + axiom audit
just site        # Build static Proof Blueprint portal at build/site/
just reproduce   # End-to-end verification + SHA-256 check + Build Standard v1.2.0 audit
```

Windows PowerShell orchestrator: `pwsh -File scripts/run_all.ps1 -Task all`. See [`REPLICATION.md`](REPLICATION.md), [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`ERRATA.md`](ERRATA.md), and [`docs/index.md`](docs/index.md).

## Maintenance Status & License

**Status: Active** (`repostatus: active`). Dual-licensed under **Apache-2.0** (code, Lean proofs, scripts, CI) and **CC-BY-4.0** (manuscript, figures, documentation); see [`LICENSE`](LICENSE), [`NOTICE`](NOTICE), and [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
