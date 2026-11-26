<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations, Epistemic Boundaries, and Real vs. Metaphor (`LIMITATIONS.md`)

This document catalogs every mathematical, formalization, computational, and tooling limitation of `p-vs-np-frontier-lab`. Nothing is hidden or swept into footnotes.

## 1. Mathematical & Complexity-Theoretic Boundaries

1. **$\mathrm{P}$ vs. $\mathrm{NP}$ Remains Completely Open:**
   No theorem in `lean/Solution.lean` and no experiment in `experiments/` proves $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$. All 14 Lean theorems establish unconditional barrier, rigidity, phase-transition, and algebraic-reversibility results.
2. **Finite-$n$ Formulation of Natural Proofs (`C3`):**
   `PVsNP.NaturalProofs.natural_proof_breaks_prf` proves the exact cross-multiplied integer distinguishing bound for arbitrary fixed input length $n$, seed length $\lambda$, and density denominator $D$. Connecting this finite-$n$ bound to an asymptotic complexity-class separation ($\mathrm{NP} \not\subseteq \mathrm{P/poly}$) additionally requires assuming a concrete family of subexponentially secure PRFs.
3. **Conditional Nature of Polymorphism Rigidity (`C9`):**
   While `monotone_3sat_only_projections` unconditionally proves that $\{R_{000}, R_{111}\}$ admits only coordinate projections across all finite arities $k \ge 1$, deducing that $\mathrm{CSP}(\{R_{000}, R_{111}\}) \notin \mathrm{P}$ still relies on Schaefer/Bulatov–Zhuk reductions together with the open hypothesis $\mathrm{P} \neq \mathrm{NP}$.
4. **Surviving Open Frontiers Are Not Resolutions:**
   Pathways 9 (characteristic-2 / GCT), 10 (catalytic space--time / Williams 2025), and 11 (bounded arithmetic / hardness magnification) survive our 5-barrier gauntlet as *non-trivial research targets*, NOT as completed separations.

## 2. Computational & Experimental Limitations

1. **Attack A (CTDS ODE) Is a `numerical_approximation`:**
   `experiments/exp4_wild_p_eq_np_falsifiers.py` integrates Ercsey-Ravasz & Toroczkai's CTDS equations via SciPy `RK45` (`float64`, `rtol=1e-7`, `atol=1e-9`). Floating-point ODE integration cannot constitute a rigorous proof of divergence; it is strictly an empirical diagnostic contrasting planted-SAT convergence ($20/20$ solved) against exhaustively UNSAT Lagrange-multiplier growth ($0/15$ solved, $\max_m \ln a_m(80) \approx 10.68$).
2. **Timeout on $\mathrm{CLIQUE}_{4,3}$ ($n=6$) in Experiment 2:**
   CaDiCaL 2.1.2 hit its 20-second per-$k$ budget deciding $\mathrm{MC}(\mathrm{CLIQUE}_{4,3}) \stackrel{?}{\le} 5$; its exact value remains $\mathrm{MC} \in \{5, 6\}$ in this artifact.
3. **Finite-Size Horizons:**
   Exact Tseitin benchmarks run up to $V=46$ (69 variables), exact MC synthesis covers $n \in \{3,4,5\}$, exhaustive Markov verification covers $k \le 4$ ($2^{15} = 32{,}768$ inputs), catalytic verification covers $d \le 8$ ($49{,}150$ ops), and exact rational Mignon–Ressayre Hessian ranks cover $n \in \{2,3,4,5\}$.

## 3. Lean 4.35 Formalization & Upstream Toolchain Limitations

1. **Upstream Windows `lean4lean.exe` Header Mismatch (`issue`):**
   The `lean4lean.exe` binary bundled inside `leanprover/lean4:v4.35.0` on Windows rejects Lean 4.35.0's own stdlib `Init.Prelude.olean` with `incompatible header`. All six kernels run cleanly on Ubuntu Linux CI via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid`.
2. **Zero-Mathlib Trade-Off:**
   Building without Mathlib guarantees minimal trusted computing base and fast multi-kernel replay, at the cost of defining bespoke finite-type combinatorics and 4-tape Oracle Turing Machine encodings from scratch.

## 4. Real vs. Metaphor

- **"Barrier Wall" / "Gauntlet":** Refers literally to the formal impossibility theorems (`C2` Relativization, `C3`–`C5` Natural Proofs, `C8`–`C9` Polymorphism Rigidity, `C10`–`C13` Circuit/Algebraic Phase Transitions) and concrete empirical counterexamples (`E7`–`E9`).
- **"Zero-Workspace Catalytic":** Refers literally to `PVsNP.CatalyticAlgebra.catalytic_multilinear_exact`, where all $d$ catalyst registers hold arbitrary integer values and are restored identically to their pre-execution state upon termination.
- **"Not Peer Reviewed":** This preprint and formalization are solo independent research with disclosed AI assistance; correctness of `C1`–`C14` rests on independent Lean 4.35.0 kernel replay, not journal peer review.
