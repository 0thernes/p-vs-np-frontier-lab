<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Machine-Auditable Claims Ledger (`CLAIMS.md`)

> **Epistemic Boundary (Non-Negotiable):** $\mathrm{P}$ vs. $\mathrm{NP}$ remains **COMPLETELY OPEN**.
> Zero claims in this repository assert $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$.

Every formalized statement below is known mathematics. The Lean library formalizes the Baker–Gill–Solovay theorem (`C1`–`C2`), the counting step of the natural-proofs argument (`C3`–`C5`), and twelve classical supporting lemmas. Only `C2` is a barrier theorem in full. Wording was corrected on 2026-11-26 to match the [statement audit](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md); see [`ERRATA.md`](ERRATA.md).

Every scientific claim in this repository is tagged with one of four verification tiers:
- **`TIER-1 (Lean 4.35 Multi-Kernel)`**: Proved in `lean/Solution.lean` (zero Mathlib; zero `sorry` in proof modules, with 15 intentional comparator stubs in `lean/PalomarChallenge.lean`; axioms $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$; accepted by 6 kernel checks with 5 checker implementations on Ubuntu CI).
- **`TIER-2 (Exact-Arithmetic / SAT-Certified)`**: Exact integer, rational (`fractions.Fraction`), $\mathbb{F}_2$, or CaDiCaL 2.1.2 SAT/UNSAT computation checked by `pytest`. Not machine-checked in Lean.
- **`TIER-3 (Numerical Approximation)`**: Adaptive `float64` RK45 ODE integration — explicitly labeled `numerical_approximation`, never cited as proof.
- **`TIER-4 (Open Frontier)`**: Explicitly unresolved conjecture or research direction.

## Tier-1 Machine-Checked Lean 4.35 Statements

| ID | Statement (`lean/Challenge.lean`) | Proof (`lean/Solution.lean`) | Exact `#print axioms` | Verification Command |
|---|---|---|---|---|
| `C1` | `PSubsetNPStmt` ($\forall O,\, \mathrm{P}^O \subseteq \mathrm{NP}^O$ in an explicit 4-tape oracle Turing machine model) | `prove_p_subset_np` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C2` | `BakerGillSolovayStmt` ($\exists A,\, \mathrm{P}^A=\mathrm{NP}^A$; $\exists B, L,\, L \in \mathrm{NP}^B \setminus \mathrm{P}^B$; same machine model, oracles are arbitrary functions) | `prove_baker_gill_solovay` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C3` | `NaturalProofBreaksPRFStmt` (counting lemma behind Razborov–Rudich: a property accepting $\ge$ numer/denom of all truth tables and rejecting every keyed-family output accepts no key and has acceptance gap $\ge$ numer/denom; no constructivity, circuit class or efficiency bound) | `prove_natural_proof_breaks_prf` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C4` | `HybridTelescopingStmt` (integer pigeonhole: $mB < \lvert a_0 - a_m\rvert \Rightarrow \exists i < m,\ \lvert a_i - a_{i+1}\rvert > B$) | `prove_hybrid_telescoping` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C5` | `NaturalProofNonvacuousStmt` (`nonConstantProp` accepts $\ge 1/2$ of all tables and rejects constants, $n \ge 1$) | `prove_natural_proof_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C6` | `OddCycleContextualStmt` ($\forall k \ge 0$, the odd-cycle XOR system on $2k+1$ variables is minimally unsatisfiable) | `prove_odd_cycle_contextual` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C7` | `MerminPeresContextualStmt` (the 9-variable Mermin–Peres parity system is minimally unsatisfiable) | `prove_mermin_peres_contextual` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C8` | `TractablePolymorphismsStmt` ($x \oplus y \oplus z$, AND, OR, majority preserve one XOR, Horn, dual-Horn, 2-clause relation each; not Schaefer's dichotomy) | `prove_tractable_polymorphisms` | `propext` | `lake build && lake env lean VerifyAxioms.lean` |
| `C9` | `Monotone3SATRigidStmt` (every operation of any arity preserving both $R_{000}$ and $R_{111}$ is a projection; dropping either admits a constant) | `prove_monotone_3sat_rigid` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C10` | `MarkovInverterTightStmt` ($\le r$ NOT gates cannot invert $n \ge 2^r$ inputs; $k$ NOT gates invert exactly $n = 2^k - 1$ inputs) | `prove_markov_inverter_tight` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C11` | `FischerReductionStmt` (every circuit on exactly $2^k - 1$ inputs has an equivalent circuit with exactly $k$ NOT gates; no size bound) | `prove_fischer_reduction` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C12` | `MultiplicativeComplexityStmt` (every wire with $a$ AND gates has $\deg_{\mathbb{F}_2} \le a+1$; $\mathrm{MC}(\mathrm{AND}_n) \ge n-1$) | `prove_multiplicative_complexity` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C13` | `PermDetChar2Stmt` ($\mathrm{Perm}_n \equiv \det_n \pmod 2$ with Laplace definitions; $W_n$ has permanent 2 and determinant 0, so they differ mod every $p \ge 3$) | `prove_perm_det_char2` | `propext`, `Classical.choice`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `C14` | `CatalyticAlgebraStmt` (reversibility of well-formed straight-line register programs; one recursive program of $3\cdot 4^{d-1} - 2$ instructions adds $\pm$ the product of $d$ program constants to one register and restores all others) | `prove_catalytic_algebra` | `propext`, `Quot.sound` | `lake build && lake env lean VerifyAxioms.lean` |
| `ALL` | `AllFrontierTheoremsStmt` ($\bigwedge_{i=1}^{14} C_i$) | `prove_all_frontier_theorems` | `propext`, `Classical.choice`, `Quot.sound` | Six kernel checks in Ubuntu CI run 45829725341 (`results/six_kernel_audit.txt` dates from v1.0.0) |

The 5 `NonVacuity` and 5 `AdversarialTests` declarations are one-line instances of `C5`, `C6`, `C7`, `C9`, `C10`, `C12`, `C13` and `C14`; `nv_mermin_peres_contextual` restates `C7` verbatim.

## Tier-2 & Tier-3 Computational Claims

| ID | Tier | Claim Summary | Source Artifact | Pytest Guard |
|---|---|---|---|---|
| `E1` | `TIER-2` | Exhaustive unary/binary/ternary census of all 15 non-empty 3-SAT clause subsets: projection-only rigidity holds iff $\{R_{000}, R_{111}\} \subseteq S$. | `results/exp1_polymorphism_contextuality.json` | `test_exp1_inclusion_minimal_rigidity` |
| `E2` | `TIER-2` | 3-regular twisted-chord Tseitin graphs ($V=10..46$) are all minimally unsatisfiable; CaDiCaL conflicts grow $64 \to 23{,}644$ while $\mathbb{F}_2$ Gaussian elimination takes $V-1$ ($9 \to 45$) row ops. | `results/exp1_polymorphism_contextuality.json` | `test_exp1_tseitin_and_mermin_peres_contextuality` |
| `E3` | `TIER-2` | CaDiCaL 2.1.2 multiplicative complexity of 19 functions ($n=3,4,5$) gives strict $\Delta=+1$ gaps above $\deg_{\mathbb{F}_2}-1$ on `Bent_4`, `E_2^5`, `E_3^5`; `CLIQUE_4_3` satisfies $\mathrm{MC} \in \{5,6\}$. These values reproduce published exhaustive classifications (Turan and Peralta, ePrint 2015/848; Calik, Turan and Peralta, Cryptogr. Commun. 11 (2019), doi:10.1007/s12095-018-0297-2). | `results/exp2_multiplicative_complexity.json` | `test_exp2_exact_mc_witnesses_and_strict_gaps` |
| `E4` | `TIER-2` | Exhaustive brute-force enumeration of all 2,048 1-AND circuits on $n=3$ (16 affine, 128 $\mathrm{MC}\le 1$, 128 $\mathrm{MC}=2$) agrees with `exp2.synthesize_mc` on every case. | `tests/test_all.py` | `test_exp2_bruteforce_sat_encoder_equivalence_n3` |
| `E5` | `TIER-2` | Constructive Markov $k$-NOT inverter verified exhaustively for $k=1..4$ up to $2^{15}=32{,}768$ inputs (0 failures); Berkowitz slice monotonicity checked on `PARITY_6` in Python only (not formalized in Lean). | `results/exp3_markov_and_catalytic.json` | `test_exp3_markov_and_catalytic_invariants` |
| `E6` | `TIER-2` | Recursive register product program checked for $d=1..8$ (0 clean registers, 0 corruptions, op count $3\cdot 4^{d-1}-2$, up to 49,150 ops). | `results/exp3_markov_and_catalytic.json` | `test_exp3_markov_and_catalytic_invariants` |
| `E7` | `TIER-3` | CTDS ODE (`RK45`, `float64`, explicitly `numerical_approximation`): solves 20/20 planted locked 3-SAT ($n=12..30$) but 0/15 exhaustively verified UNSAT 3-SAT ($n=5,10,12$), with $\max_m \ln a_m(80) \approx 10.68$ ($a_{\max} \approx 4.35\times 10^4$). A numerical illustration, not a counterexample. | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E8` | `TIER-2` | Exact rational (`Fraction`) LP relaxation achieves clause-sum $\ge 1$ ($1, 3/2, 3/2$) on three exhaustively UNSAT formulas ($C_3$, Mermin–Peres, 8-clause 3-CNF). This is elementary: $x_i = 1/2$ satisfies the clause LP of every 3-CNF. | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E9` | `TIER-2` | Exact 3-adic Hensel lift on duplicate-free 10-clause UNSAT 3-SAT yields root $[42,0,0,0] \pmod{81} \to (3/2,0,0,0) \in \mathbb{Z}_3^4$ (non-Boolean). Rigid 15-clause UNSAT 3-SAT ($n=5$) has $|\mathrm{Aut}(\Phi)| = 1$ over all 3,840 signed permutations and 5/5 1-WL colors. | `results/exp4_wild_p_eq_np_falsifiers.json` | `test_exp4_wild_p_eq_np_falsifiers` |
| `E10` | `TIER-2` | Exact integer char-2 $\mathrm{Perm}_n \equiv \det_n \pmod 2$ ($n=2..5$), $W_n$ witness mod 3, and exact rational Mignon–Ressayre Hessian ranks $n^2 \in \{4,9,16,25\}$ giving $\mathrm{dc}(\mathrm{Perm}_n) \ge \lceil n^2/2\rceil \in \{2,5,8,13\}$. | `results/exp5_char2_and_hessian.json` | `test_exp5_char2_and_mignon_ressayre_hessian` |

`E7`–`E9` together are three exact counterexamples and one numerical illustration against four illustrative SAT heuristics built for this bench. Only Attack A (`E7`) follows a published method (Ercsey-Ravasz and Toroczkai 2011); the other three have no published proposer.

## Tier-4 Open Frontiers

- **`O1`**: $\mathrm{P} \stackrel{?}{=} \mathrm{NP}$ (completely open).
- **`O2`**: Exact multiplicative complexity of $\mathrm{CLIQUE}_{4,3}$ ($n=6$): not determined in this artifact, where it is bracketed at $\mathrm{MC} \in \{5, 6\}$ (`k=5` timed out at 20 s in CaDiCaL 2.1.2). It is not open in the literature: Calik, Turan and Peralta (2019) computed the multiplicative complexity of all affine equivalence classes of 6-variable Boolean functions.
- **`O3`**: Extending Pathways 9 (GCT / permanent vs. determinant), 10 (catalytic space--time simulations beyond Williams 2025 $\mathrm{TIME}[t] \subseteq \mathrm{SPACE}[\sqrt{t\log t}]$), and 11 (bounded arithmetic / hardness magnification past the locality barrier) to unconditional superpolynomial circuit lower bounds.

## Prior Work and Attribution

- `C1`–`C2`: Baker, Gill, Solovay, SIAM J. Comput. 4(4) (1975) 431–442, doi:10.1137/0204037.
- `C3`–`C5`: Razborov, Rudich, J. Comput. Syst. Sci. 55(1) (1997) 24–35, doi:10.1006/jcss.1997.1494. Only the counting step is formalized.
- `C6`–`C7`: odd-cycle parity and the Mermin–Peres square (Mermin 1990; Peres 1990); the "maximal contextuality" terminology is from Abramsky and Brandenburger, New J. Phys. 13 (2011) 113036, arXiv:1102.0264, whose sheaf-theoretic notion is not formalized here.
- `C8`–`C9`: Schaefer (STOC 1978) and Post's lattice (clones $T_0$, $T_1$). `C9` is a classical fact given a new Lean proof.
- `C10`–`C11`: Markov, J. ACM 5(4) (1958) 331–334, doi:10.1145/320941.320945; Fischer, LNCS 33 (1975) 71–82, doi:10.1007/3-540-07407-4_9. Fischer's theorem is a polynomial-size construction; `C11` has no size bound.
- `C12`: Boyar, Peralta, Theoret. Comput. Sci. 396 (2008) 223–246, doi:10.1016/j.tcs.2008.01.030.
- `C13`: Valiant, The complexity of computing the permanent, Theoret. Comput. Sci. (1979), doi:10.1016/0304-3975(79)90044-6. No hardness notion for the permanent is formalized.
- `C14`: Ben-Or, Cleve, SIAM J. Comput. 21 (1992), doi:10.1137/0221006 (register programs of polynomial length with three registers); Buhrman, Cleve, Koucký, Loff, Speelman, STOC 2014 (catalytic space).
- `E3`, `O2`: Turan, Peralta, ePrint 2015/848; Calik, Turan, Peralta, Cryptogr. Commun. 11 (2019), doi:10.1007/s12095-018-0297-2.
