<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Machine-Auditable Claims Ledger (`CLAIMS.md`)

> **Epistemic Boundary (Non-Negotiable):** $\mathrm{P}$ vs. $\mathrm{NP}$ remains **COMPLETELY OPEN**.
> Zero claims in this repository assert $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$.

Every scientific claim in this repository is tagged with one of four verification tiers:
- **`TIER-1 (Lean 4.35 Multi-Kernel)`**: Formally verified in `lean/Solution.lean` (zero Mathlib, zero `sorry`, axioms $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$, 6 passing kernel checks across 5 independent codebases).
- **`TIER-2 (Exact-Arithmetic / SAT-Certified)`**: 100% exact integer, rational (`fractions.Fraction`), $\mathbb{F}_2$, or CaDiCaL 2.1.2 SAT/UNSAT computation verified by `pytest`.
- **`TIER-3 (Numerical Approximation)`**: Adaptive `float64` RK45 ODE integration — explicitly labeled `numerical_approximation`, never cited as proof.
- **`TIER-4 (Open Frontier)`**: Explicitly unresolved conjecture or research direction.

## Tier-1 Machine-Checked Lean 4.35 Theorems

| ID | Statement (`lean/Challenge.lean`) | Proof (`lean/Solution.lean`) | Exact `#print axioms` | Verification Command |
|---|---|---|---|---|
| `C1` | `PSubsetNPStmt` ($\forall O,\, \mathrm{P}^O \subseteq \mathrm{NP}^O$) | `prove_p_subset_np` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C2` | `BakerGillSolovayStmt` ($\exists A,B,\, \mathrm{P}^A=\mathrm{NP}^A \land \mathrm{P}^B\neq\mathrm{NP}^B$) | `prove_baker_gill_solovay` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C3` | `NaturalProofBreaksPRFStmt` (exact cross-multiplied $\mathbb{Z}$ PRF break) | `prove_natural_proof_breaks_prf` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C4` | `HybridTelescopingStmt` (exact $\mathbb{Z}$ hybrid triangle inequality) | `prove_hybrid_telescoping` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C5` | `NaturalProofNonVacuousStmt` (`nonConstantProp` density $\ge 1/2$) | `prove_natural_proof_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C6` | `OddCycleContextualStmt` ($\forall k,\, C_{2k+3}$ maximally contextual) | `prove_odd_cycle_contextual` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C7` | `MerminPeresContextualStmt` (3×3 magic square maximally contextual) | `prove_mermin_peres_contextual` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C8` | `TractablePolymorphismsStmt` (Maltsev XOR, Horn AND, Dual-Horn OR, 2-SAT Maj) | `prove_tractable_polymorphisms` | `propext` | `lake build && lake env lean VerifyAxioms.lean` |
| `C9` | `Monotone3SATRigidStmt` ($\forall k \ge 1$, $\{R_{000},R_{111}\}$ inclusion-minimal rigid) | `prove_monotone_3sat_rigid` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C10` | `MarkovInverterTightStmt` ($k$ NOT gates invert $n$ bits $\iff n \le 2^k - 1$) | `prove_markov_inverter_tight` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C11` | `FischerReductionStmt` (universal dual-rail compilation to $\le k$ NOT gates) | `prove_fischer_reduction` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C12` | `MultiplicativeComplexityStmt` ($\deg_{\mathbb{F}_2}(f) \le k+1$, $\mathrm{MC}(\mathrm{AND}_n) \ge n-1$) | `prove_multiplicative_complexity` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C13` | `PermDetChar2Stmt` (mod-2 collapse + $W_n$ separating mod all $p \ge 3$) | `prove_perm_det_char2` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C14` | `CatalyticAlgebraStmt` (bijective reversibility + exact $3\cdot 4^{d-1}$ $d$-fold zero-workspace product) | `prove_catalytic_algebra` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `ALL` | `AllFrontierTheoremsStmt` ($\bigwedge_{i=1}^{14} C_i$) | `prove_all_frontier_theorems` | `propext`, `Classical.choice`, `Quot.sound` | Passed 6 kernels (`results/six_kernel_audit.txt`) |

## Tier-2 & Tier-3 Computational Claims

| ID | Tier | Claim Summary | Source Artifact | Pytest Guard |
|---|---|---|---|---|
| `E1` | `TIER-2` | Exhaustive unary/binary/ternary census of all 15 non-empty 3-SAT clause subsets: projection-only rigidity holds iff $\{R_{000}, R_{111}\} \subseteq S$. | `results/exp1_polymorphism_contextuality.json` | `test_exp1_inclusion_minimal_rigidity` |
| `E2` | `TIER-2` | 3-regular twisted-chord Tseitin graphs ($V=10..46$) are all maximally contextual; CaDiCaL conflicts explode $64 \to 23{,}644$ while $\mathbb{F}_2$ Gaussian elimination takes $V-1$ ($9 \to 45$) row ops. | `results/exp1_polymorphism_contextuality.json` | `test_exp1_tseitin_and_mermin_peres_contextuality` |
| `E3` | `TIER-2` | Exact CaDiCaL 2.1.2 Multiplicative Complexity on 19 functions ($n=3,4,5$) reveals certified strict $\Delta=+1$ gaps above $\deg_{\mathbb{F}_2}-1$ on `Bent_4`, `E_2^5`, `E_3^5`; `CLIQUE_4_3` satisfies $\mathrm{MC} \in \{5,6\}$. | `results/exp2_multiplicative_complexity.json` | `test_exp2_exact_mc_witnesses_and_strict_gaps` |
| `E4` | `TIER-2` | Exhaustive brute-force enumeration of all 2,048 1-AND circuits on $n=3$ (16 affine, 128 $\mathrm{MC}\le 1$, 128 $\mathrm{MC}=2$) agrees 100% with `exp2.synthesize_mc`. | `tests/test_all.py` | `test_exp2_bruteforce_sat_encoder_equivalence_n3` |
| `E5` | `TIER-2` | Constructive Markov $k$-NOT inverter verified exhaustively for $k=1..4$ up to $2^{15}=32{,}768$ inputs (0 failures); Berkowitz slice monotonicity verified on `PARITY_6`. | `results/exp3_markov_and_catalytic.json` | `test_exp3_markov_and_catalytic_invariants` |
| `E6` | `TIER-2` | Zero-workspace catalytic $d$-fold multilinear product verified for $d=1..8$ (0 clean regs, 0 corruptions, exact op count $3\cdot 4^{d-1}-2$, up to 49,150 ops). | `results/exp3_markov_and_catalytic.json` | `test_exp3_markov_and_catalytic_invariants` |
| `E7` | `TIER-3` | CTDS ODE (`RK45`, `float64`, explicitly `numerical_approximation`): solves 20/20 planted locked 3-SAT ($n=12..30$) but 0/15 exhaustively verified UNSAT 3-SAT ($n=5,10,12$), with $\max_m \ln a_m(80) \approx 10.68$ ($a_{\max} \approx 4.35\times 10^4$). | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E8` | `TIER-2` | Exact rational (`Fraction`) LP relaxation achieves clause-sum $\ge 1$ ($1, 3/2, 3/2$) on three exhaustively UNSAT formulas ($C_3$, Mermin–Peres, 8-clause 3-CNF). | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E9` | `TIER-2` | Exact 3-adic Hensel lift on duplicate-free 10-clause UNSAT 3-SAT yields root $[42,0,0,0] \pmod{81} \to (3/2,0,0,0) \in \mathbb{Z}_3^4$ (non-Boolean). Rigid 15-clause UNSAT 3-SAT ($n=5$) has $|\mathrm{Aut}(\Phi)| = 1$ over all 3,840 signed permutations and 5/5 1-WL colors. | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E10` | `TIER-2` | Exact integer char-2 $\mathrm{Perm}_n \equiv \det_n \pmod 2$ ($n=2..5$), $W_n$ witness mod 3, and exact rational Mignon–Ressayre Hessian ranks $n^2 \in \{4,9,16,25\}$ giving $\mathrm{dc}(\mathrm{Perm}_n) \ge \lceil n^2/2\rceil \in \{2,5,8,13\}$. | `results/exp5_char2_and_hessian.json` | `test_exp5_char2_and_mignon_ressayre_hessian` |

## Tier-4 Open Frontiers (Explicitly Unresolved)

- **`O1`**: $\mathrm{P} \stackrel{?}{=} \mathrm{NP}$ (completely open).
- **`O2`**: Exact multiplicative complexity of $\mathrm{CLIQUE}_{4,3}$ ($n=6$): bracketed at $\mathrm{MC} \in \{5, 6\}$ (`k=5` timed out at 20 s in CaDiCaL 2.1.2).
- **`O3`**: Extending Pathways 9 (GCT / permanent vs. determinant), 10 (catalytic space--time simulations beyond Williams 2025 $\mathrm{TIME}[t] \subseteq \mathrm{SPACE}[\sqrt{t\log t}]$), and 11 (bounded arithmetic / hardness magnification past the locality barrier) to unconditional superpolynomial circuit lower bounds.
