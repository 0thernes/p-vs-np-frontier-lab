<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# P vs. NP Frontier & Barrier Anatomy Lab (`p-vs-np-frontier-lab`)

[![CI](https://github.com/0thernes/p-vs-np-frontier-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/p-vs-np-frontier-lab/actions/workflows/ci.yml)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-A6CE39.svg)](https://orcid.org/0009-0006-8168-9648)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0_%7C_6_kernel_checks-2ea44f.svg)](lean/Challenge.lean)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/License-Apache--2.0_%2F_CC--BY--4.0-blue.svg)](LICENSE)
[![Project Status: Active](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)

A zero-Mathlib Lean 4.35.0 formalization of the Baker–Gill–Solovay oracle theorem, the counting step of the natural-proofs argument, and twelve classical supporting lemmas, together with exact-arithmetic and SAT experiments and a 15-page AMS-LaTeX preprint that surveys twelve proposed pathways toward $\mathrm{P}$ vs. $\mathrm{NP}$. All formalized results are known mathematics; no new theorem is claimed.

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID: [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648))  
**Version:** `1.2.0` · **Archive Entry:** `0TH-2026-013` in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) · **Blueprint:** [Interactive Proof Blueprint](https://0thernes.github.io/p-vs-np-frontier-lab/) · **Citations:** 27 references; three DOIs in [`docs/citation-audit.md`](docs/citation-audit.md) resolve to unrelated papers (correction pending, see [`ERRATA.md`](ERRATA.md))

> ### Epistemic Scope Boundary (Explicit Non-Claim)
> **$\mathrm{P}$ vs. $\mathrm{NP}$ remains completely open.** Nothing in this repository claims a proof of $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$.  
> This repository delivers:
> 1. **Tier 1 (machine-checked in Lean 4.35):** 14 statements `C1`–`C14` (the Baker–Gill–Solovay theorem, the counting step of natural proofs, and 12 classical supporting lemmas), their conjunction, and 10 instantiated corollaries (5 in `NonVacuity`, 5 in `AdversarialTests`): 25 audited declarations in all. Zero Mathlib, `module` headers, `autoImplicit = false`, zero custom axioms. Zero `sorry` in proof modules; `lean/PalomarChallenge.lean` holds 15 intentional `sorry` stubs for the comparator and is not a default build target. On Ubuntu CI the proofs are accepted by six kernel checks with five checker implementations (the Lean reference kernel in default and paranoid mode, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid`. CI also runs a negative elaboration test: a false statement must fail to compile. That test is rejected by the `decide` tactic during elaboration, not by the kernel.
> 2. **Tier 2 (exact-arithmetic and SAT computations):** 4 exact integer/rational/$\mathbb{F}_2$/CaDiCaL 2.1.2 experiments with a `pytest` suite (including an exhaustive brute-force SAT-encoder check on $n=3$, Hypothesis property tests, and negative/mutant checks). The multiplicative-complexity values of experiment E3 reproduce published exhaustive classifications (Turan and Peralta; Calik, Turan and Peralta 2019).
> 3. **Tier 3 (tagged `numerical_approximation`):** an adaptive `float64` RK45 ODE run for Attack A (the CTDS solver of Ercsey-Ravasz and Toroczkai 2011). It contrasts convergence on planted satisfiable instances with growth of the auxiliary weights on exhaustively verified unsatisfiable instances. It is an illustration, not a proof. Experiment 4 as a whole gives three exact counterexamples and one numerical illustration against four illustrative SAT heuristics built for the bench; only Attack A follows a published method.
> 4. **Tier 4 (white paper):** 15-page frozen PDF ([`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`](dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf)) and arXiv source tarball ([`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)). Statements in the frozen paper that overstate the Lean results are corrected in [`ERRATA.md`](ERRATA.md).

---

## Axiom and Kernel Check

Rebuild and check every theorem in `lean/Solution.lean` from scratch (requires Lean `v4.35.0`, no Mathlib download):

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

This ledger was written for v1.0.0 (13 Lean files, 8,078 lines) and has not been regenerated for v1.2.0 (17 files, 8,266 lines). For v1.2.0 the six kernel checks rest on the log of CI run [45829725341](https://github.com/0thernes/p-vs-np-frontier-lab/actions/runs/45829725341). The Lean default and paranoid checks use the same reference kernel, so six checks correspond to five checker implementations.

| Checker / Kernel | Implementation | Exit | Verdict |
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
| `C1` | `PVsNP.OTM` | `PSubsetNPStmt` / `prove_p_subset_np` | $\forall O,\; \mathrm{P}^O \subseteq \mathrm{NP}^O$ in an explicit 4-tape oracle Turing machine model with $(n+1)^c + c$ step bounds |
| `C2` | `PVsNP.Relativization` | `BakerGillSolovayStmt` / `prove_baker_gill_solovay` | $\exists A,\; \mathrm{P}^A = \mathrm{NP}^A$ and $\exists B, L,\; L \in \mathrm{NP}^B \setminus \mathrm{P}^B$ (oracles are arbitrary functions; this machine model only) |
| `C3` | `PVsNP.NaturalProofs` | `NaturalProofBreaksPRFStmt` / `prove_natural_proof_breaks_prf` | Counting lemma behind Razborov–Rudich: a property accepting $\ge$ numer/denom of all truth tables and rejecting every keyed-family output accepts no key (constructivity, circuit class and distinguisher complexity not formalized) |
| `C4` | `PVsNP.NaturalProofs` | `HybridTelescopingStmt` / `prove_hybrid_telescoping` | Integer pigeonhole bound: if $mB < \lvert a_0 - a_m\rvert$ then $\lvert a_i - a_{i+1}\rvert > B$ for some $i < m$ |
| `C5` | `PVsNP.NaturalProofs` | `NaturalProofNonvacuousStmt` / `prove_natural_proof_nonvacuous` | `nonConstantProp` accepts $\ge 1/2$ of all tables and rejects constants, for all $n \ge 1$ |
| `C6` | `PVsNP.SheafPolymorphism` | `OddCycleContextualStmt` / `prove_odd_cycle_contextual` | For all $k \ge 0$ the odd-cycle XOR system on $2k+1$ variables is minimally unsatisfiable (named "maximally contextual" in the code) |
| `C7` | `PVsNP.SheafPolymorphism` | `MerminPeresContextualStmt` / `prove_mermin_peres_contextual` | The 9-variable Mermin–Peres parity system is minimally unsatisfiable |
| `C8` | `PVsNP.SheafPolymorphism` | `TractablePolymorphismsStmt` / `prove_tractable_polymorphisms` | $x \oplus y \oplus z$, AND, OR and majority each preserve one XOR, Horn, dual-Horn and 2-clause relation (not Schaefer's dichotomy theorem) |
| `C9` | `PVsNP.SheafPolymorphism` | `Monotone3SATRigidStmt` / `prove_monotone_3sat_rigid` | Every Boolean operation of any arity preserving both $x \lor y \lor z$ and $\lnot x \lor \lnot y \lor \lnot z$ is a projection; dropping either relation admits a constant (a classical fact about Post's lattice) |
| `C10` | `PVsNP.CircuitPhaseTransition` | `MarkovInverterTightStmt` / `prove_markov_inverter_tight` | No circuit with $\le r$ NOT gates inverts $n \ge 2^r$ inputs; an explicit circuit with $k$ NOT gates inverts exactly $2^k - 1$ inputs |
| `C11` | `PVsNP.CircuitPhaseTransition` | `FischerReductionStmt` / `prove_fischer_reduction` | Every circuit on exactly $2^k - 1$ inputs has an equivalent circuit with exactly $k$ NOT gates (no size bound; not Fischer's polynomial-size theorem) |
| `C12` | `PVsNP.CircuitPhaseTransition` | `MultiplicativeComplexityStmt` / `prove_multiplicative_complexity` | Every wire of a $\{\text{const}, \oplus, \land\}$ circuit with $a$ AND gates has $\deg_{\mathbb{F}_2} \le a + 1$; so $\mathrm{MC}(\mathrm{AND}_n) \ge n - 1$ |
| `C13` | `PVsNP.CircuitPhaseTransition` | `PermDetChar2Stmt` / `prove_perm_det_char2` | $\mathrm{Perm}_n \equiv \det_n \pmod 2$ (Laplace definitions); for $n \ge 2$ one 0/1 matrix $W_n$ has permanent 2 and determinant 0, so they differ mod every $p \ge 3$ |
| `C14` | `PVsNP.CatalyticAlgebra` | `CatalyticAlgebraStmt` / `prove_catalytic_algebra` | Reversed inverted program undoes any well-formed straight-line register program; one recursive program of $3\cdot 4^{d-1} - 2$ instructions adds $\pm$ the product of $d$ integers fixed in the program to one register and restores all others |

## Relation to Prior Work

Every statement above is a known result or an elementary special case of one. `C1`–`C2` are the theorem of Baker, Gill and Solovay (SIAM J. Comput. 4 (1975), [doi:10.1137/0204037](https://doi.org/10.1137/0204037)). `C3`–`C5` formalize only the counting step of Razborov and Rudich (J. Comput. Syst. Sci. 55 (1997), [doi:10.1006/jcss.1997.1494](https://doi.org/10.1006/jcss.1997.1494)). `C9` is the classical description of the clones $T_0$ and $T_1$ in Post's lattice. `C10` is Markov's bound (J. ACM 5 (1958), [doi:10.1145/320941.320945](https://doi.org/10.1145/320941.320945)); Fischer's theorem (LNCS 33 (1975) 71–82, [doi:10.1007/3-540-07407-4_9](https://doi.org/10.1007/3-540-07407-4_9)) is a polynomial-size construction, which `C11` does not reach. For `C14`, register programs of polynomial length with three registers go back to Ben-Or and Cleve (SIAM J. Comput. 21 (1992), [doi:10.1137/0221006](https://doi.org/10.1137/0221006)); catalytic space is due to Buhrman, Cleve, Koucký, Loff and Speelman (STOC 2014). The multiplicative-complexity values of experiment E3 were computed earlier by Turan and Peralta (four and five variables, ePrint 2015/848) and by Calik, Turan and Peralta (all 6-variable functions, Cryptogr. Commun. 11 (2019), [doi:10.1007/s12095-018-0297-2](https://doi.org/10.1007/s12095-018-0297-2)). Earlier machine formalizations of Baker–Gill–Solovay were not searched for.

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

Windows PowerShell orchestrator: `pwsh -File scripts/run_all.ps1 -Task all`. The `lake check` and `lake comparator` steps need Linux with bubblewrap. See [`REPLICATION.md`](REPLICATION.md), [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`ERRATA.md`](ERRATA.md), and [`docs/index.md`](docs/index.md). The wording of this README follows the [2026-11-26 statement audit](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md).

## Maintenance Status & License

**Status: Active** (`repostatus: active`). Dual-licensed under **Apache-2.0** (code, Lean proofs, scripts, CI) and **CC-BY-4.0** (manuscript, figures, documentation); see [`LICENSE`](LICENSE), [`NOTICE`](NOTICE), and [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
