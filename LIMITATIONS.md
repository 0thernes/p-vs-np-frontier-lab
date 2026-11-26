<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations, Epistemic Boundaries, and Real vs. Metaphor (`LIMITATIONS.md`)

This document lists the mathematical, formalization, computational, and tooling limitations of `p-vs-np-frontier-lab`. Items 1.5–1.11 and 3.3–3.6 were added after the [2026-11-26 statement audit](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md).

## 1. Mathematical & Complexity-Theoretic Boundaries

1. **$\mathrm{P}$ vs. $\mathrm{NP}$ Remains Completely Open:**
   No theorem in `lean/Solution.lean` and no experiment in `experiments/` proves $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$. The 14 Lean statements are the Baker–Gill–Solovay theorem (`C1`–`C2`), the counting step of the natural-proofs argument (`C3`–`C5`), and twelve classical supporting lemmas (`C6`–`C14`). Only `C2` is a barrier theorem in full. All of them are known mathematics.
2. **Natural Proofs: Only the Counting Step (`C3`):**
   `PVsNP.NaturalProofs.natural_proof_breaks_prf` proves an exact integer counting bound for fixed input length $n$, key length $k$, and density numer/denom. `CombProperty` is an arbitrary function `List Bool → Bool`, and `PRFFamily` carries only an evaluation map, with no hardness assumption. Constructivity, a circuit class, pseudorandomness, and asymptotics are not formalized, so the "distinguisher" has no efficiency bound and `C3` is not the Razborov–Rudich theorem. Connecting it to $\mathrm{NP} \not\subseteq \mathrm{P/poly}$ would need all of these, plus a concrete family of subexponentially secure PRFs.
3. **Conditional Nature of Polymorphism Rigidity (`C9`):**
   `monotone_3sat_only_projections` proves that $\{R_{000}, R_{111}\}$ admits only coordinate projections at every finite arity $k \ge 1$. This is a classical fact about Post's lattice (the clones $T_0$ and $T_1$); Lean gives a new proof of a known result. Deducing that $\mathrm{CSP}(\{R_{000}, R_{111}\}) \notin \mathrm{P}$ still relies on Schaefer/Bulatov–Zhuk reductions together with the open hypothesis $\mathrm{P} \neq \mathrm{NP}$.
4. **Surviving Open Frontiers Are Not Resolutions:**
   Pathways 9 (characteristic-2 / GCT), 10 (catalytic space--time / Williams 2025), and 11 (bounded arithmetic / hardness magnification) are listed as research directions, NOT as completed separations.
5. **Machine Model (`C1`–`C2`):**
   The statements hold in this repository's 4-tape oracle Turing machine model with $(n+1)^c + c$ step bounds. Equivalence with other machine models is not formalized. Oracles are arbitrary functions `List Bool → Bool`; docstrings that call them "computable" describe the construction, not the statement.
6. **Hybrid Bound (`C4`):**
   Lean proves the pigeonhole form (if $mB < \lvert a_0 - a_m\rvert$ then some step exceeds $B$), not the summed triangle inequality stated in the paper.
7. **"Maximally Contextual" Means Minimally Unsatisfiable (`C6`–`C7`):**
   `IsMaximallyContextual` is defined as "unsatisfiable, and every drop-one subsystem is satisfiable". No presheaf, empirical model or cohomology is formalized. `oddCycleSystem k` has $2k+1$ variables, so $k = 0$ is the one-variable system $x_0 \oplus x_0 = 1$ and the triangle is $k = 1$.
8. **Polymorphism Facts Are Not Schaefer's Dichotomy (`C8`):**
   `C8` checks four preservation facts (one relation each for XOR, Horn, dual-Horn and 2-SAT). No CSP complexity and no dichotomy theorem is formalized.
9. **Negation-Limited Circuits (`C10`–`C11`):**
   The upper bound and the compilation cover $n = 2^k - 1$ inputs exactly, not all $n \le 2^k - 1$. `C11` proves existence of an equivalent circuit with exactly $k$ NOT gates and no size bound; the inverter built by `compileMonotoneAux` is exponential-size. Fischer's 1975 theorem is a polynomial-size construction, so `C11` is essentially the existence part of Markov's theorem, not Fischer's reduction.
10. **Permanent and Determinant (`C12`–`C13`):**
   Permanent and determinant are defined by first-row Laplace expansion; equality with the Leibniz formulas is not proved. No hardness notion for the permanent is formalized.
11. **Register Programs (`C14`):**
   In `catalyticProdProg` the multiplicands are constants written into the program, so the value added to the destination register is a fixed integer; inputs are not read from registers. The non-trivial content is that all other registers are restored whatever their initial contents. No space or time model and no catalytic-space bound is formalized. The program has $3\cdot 4^{d-1} - 2$ instructions. Ben-Or and Cleve (SIAM J. Comput. 21, 1992, doi:10.1137/0221006) give register programs of polynomial length with three registers, which is closer prior work.

## 2. Computational & Experimental Limitations

1. **Attack A (CTDS ODE) Is a `numerical_approximation`:**
   `experiments/exp4_wild_p_eq_np_falsifiers.py` integrates Ercsey-Ravasz & Toroczkai's CTDS equations via SciPy `RK45` (`float64`, `rtol=1e-7`, `atol=1e-9`). Floating-point ODE integration cannot constitute a rigorous proof of divergence; it is strictly an empirical diagnostic contrasting planted-SAT convergence ($20/20$ solved) against exhaustively UNSAT Lagrange-multiplier growth ($0/15$ solved, $\max_m \ln a_m(80) \approx 10.68$).
2. **Timeout on $\mathrm{CLIQUE}_{4,3}$ ($n=6$) in Experiment 2:**
   CaDiCaL 2.1.2 hit its 20-second per-$k$ budget deciding $\mathrm{MC}(\mathrm{CLIQUE}_{4,3}) \stackrel{?}{\le} 5$; its exact value remains $\mathrm{MC} \in \{5, 6\}$ in this artifact only. Calik, Turan and Peralta (Cryptogr. Commun. 11, 2019, doi:10.1007/s12095-018-0297-2) computed the multiplicative complexity of all affine equivalence classes of 6-variable functions, and Turan and Peralta (ePrint 2015/848) did so for four and five variables; the E3 values reproduce known results.
3. **Finite-Size Horizons:**
   Exact Tseitin benchmarks run up to $V=46$ (69 variables), exact MC synthesis covers $n \in \{3,4,5\}$, exhaustive Markov verification covers $k \le 4$ ($2^{15} = 32{,}768$ inputs), catalytic verification covers $d \le 8$ ($49{,}150$ ops), and exact rational Mignon–Ressayre Hessian ranks cover $n \in \{2,3,4,5\}$.
4. **The Four Heuristics Are Illustrative:**
   Experiment 4 gives three exact counterexamples (LP relaxation, 3-adic Hensel lifting, symmetry/1-WL) and one numerical illustration (CTDS). The heuristics were built for the bench; only the CTDS solver follows a published method. The LP counterexample is elementary, since $x_i = 1/2$ satisfies the clause LP of every 3-CNF.
5. **Not Examined by the 2026-11-26 Audit:**
   The numerical correctness of the Python experiments was not re-run against published tables.

## 3. Lean 4.35 Formalization & Upstream Toolchain Limitations

1. **Upstream Windows `lean4lean.exe` Header Mismatch (`issue`):**
   The `lean4lean.exe` binary bundled inside `leanprover/lean4:v4.35.0` on Windows rejects Lean 4.35.0's own stdlib `Init.Prelude.olean` with `incompatible header`. The six kernel checks run on Ubuntu Linux CI via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid`; these steps need Linux with bubblewrap.
2. **Zero-Mathlib Trade-Off:**
   Building without Mathlib keeps the trusted base small and multi-kernel replay fast, at the cost of defining bespoke finite-type combinatorics and 4-tape Oracle Turing Machine encodings from scratch.
3. **Six Checks, Five Implementations:**
   The Lean default and paranoid checks use the same reference kernel. `results/six_kernel_audit.txt` dates from v1.0.0 (13 files, 8,078 lines) and has not been regenerated for v1.2.0 (17 files, 8,266 lines); the v1.2.0 result rests on the log of CI run 45829725341. During `lake check` that log shows nanoda printing `Skipped exported but unpermitted axioms ["sorryAx"]` before accepting; what this line means has not been established.
4. **Negative Test Is Elaboration-Level:**
   The CI negative test feeds a false statement proved `by decide`. It is rejected by the `decide` tactic during elaboration, so no proof term reaches the kernel, and the step passes on any non-zero exit (an import or syntax error would also pass).
5. **Citation Check:**
   `scripts/check_citations.py` counts any successful Crossref lookup as verified without comparing titles, and CI runs it with `--offline` (key parity only). Three DOIs in it and in `docs/citation-audit.md` resolve to unrelated papers; see `ERRATA.md`.
6. **Sorry Stubs:**
   `lean/PalomarChallenge.lean` contains 15 intentional `sorry` stubs (the comparator's challenge side). It is excluded from `defaultTargets`; proof modules contain no `sorry`.

## 4. Real vs. Metaphor

- **"Barrier Wall" / "Gauntlet":** Refers to `C2` (relativization) and the counting step `C3`–`C5` of natural proofs. `C8`–`C13` are classical supporting lemmas, not barrier theorems. The empirical items `E7`–`E9` are counterexamples to illustrative heuristics.
- **"Zero-Workspace Catalytic":** Refers to `PVsNP.CatalyticAlgebra.catalytic_multilinear_exact`, where all non-destination registers hold arbitrary integer values and are restored to their pre-execution state upon termination. The multiplicands are program constants, and no catalytic-space complexity bound is claimed.
- **"Not Peer Reviewed":** This preprint and formalization are solo independent research with disclosed AI assistance; correctness of `C1`–`C14` rests on Lean kernel replay, not journal peer review.
