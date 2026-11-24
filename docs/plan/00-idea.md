# P0 Idea & Reframing (`p-vs-np-frontier-lab`)

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

## P0.01 One-liner
For theoretical computer scientists, formal-methods engineers, and independent researchers investigating the `P vs NP` problem, `p-vs-np-frontier-lab` eliminates unverified speculation and naive barrier-violating proof claims by delivering a unified, six-kernel Lean 4.35.0 formalization of five structural barrier/phase-transition theorems alongside an exact-arithmetic computational falsification engine auditing 12 unconventional attack pathways.

## P0.02 Remarkable Angles (Purple Cow)
1. **Six-kernel formalization of Baker–Gill–Solovay (both collapse and separation oracles)** on an explicit, unweakened 3-tape Oracle Turing Machine model with zero Mathlib dependencies.
2. **Formal refutation of naive sheaf-cohomological / contextuality `P ≠ NP` proofs** by proving in Lean 4 that infinite odd-cycle XOR-SAT families and the Mermin–Peres magic square are maximally contextual ($H^1 \neq 0$, locally consistent on every proper subset, zero global section) yet live inside `P` — coupled with an all-arity proof that 3-SAT polymorphisms collapse to dictators.
3. **Exact Markov–Fischer bounded-negation phase transition + Multiplicative Complexity degree wall** formalized in Lean 4.35.0: bridging the razor-thin $\lceil \log_2(n+1) \rceil$ NOT-gate chasm between proved exponential monotone lower bounds and full `NP ⊄ P/poly`.
4. **Exact catalytic zero-workspace multilinear algebra (Cook–Mertz / Williams 2025 mechanism)** formalized in Lean 4 alongside an explicit accounting of why catalytic space compression trades space for exponential uncomputation time rather than collapsing `NP` to `P`.
5. **Adversarial experimental falsification of 4 wild `P = NP` algorithmic attacks** (continuous-time ODE Lagrange blowup, exact-rational LP/Sherali–Adams integrality gaps, $p$-adic Hensel Jacobian drop, and asymmetric rigid 3-SAT instances defeating Weisfeiler–Leman symmetry breaking), plus CaDiCaL SAT-based exact Multiplicative Complexity synthesis hunting for $\mathrm{MC}(f) > \deg(f) - 1$.

**Chosen angle:** Unified synthesis of all 5 into one reproducible, zero-Mathlib, six-kernel-verified laboratory and AMS-LaTeX monograph — because `P vs NP` is uniquely defined by the *intersection* of its barriers, not any single isolated trick.

## P0.03 Reframes (Conceptual Blockbusting)
1. **Instead of "attempt a direct proof of P ≠ NP"**: Treat every unconventional attack (sheaves, contextuality, tropical algebra, thermodynamics, ultrametrics, catalytic memory, continuous ODEs, $p$-adic lifting) as a *falsifiable hypothesis*, push it until it either yields a kernel-checked theorem or hits a sharp counterexample, and formalize the resulting obstruction!
2. **Instead of "informal barrier survey"**: Turn the barrier wall itself into executable, machine-checked mathematics (`Challenge.lean` vs `Solution.lean` under `lake comparator --paranoid`) where every hypothesis is witnessed non-vacuously.
3. **Instead of "black-box floating-point heuristics"**: Use exact integer / rational / $\mathbb{F}_2$ / CaDiCaL SAT synthesis so every empirical gap and threshold is cryptographically reproducible and immune to float64 illusions.

## P0.04–P0.05 Upside, Margin of Safety, and Go Decision
- **Best case:** Discover sharp exact structural separations (e.g., exact minimal clause subsets forcing polymorphism rigidity, exact small-$n$ multiplicative-complexity gaps exceeding $\deg(f)-1$, and a flagship zero-Mathlib 6-kernel Lean 4.35.0 library covering BGS + Natural Proofs + Sheaf/Polymorphism + Markov–Fischer + Catalytic Algebra) suitable for Palomar Registry, Zenodo, and peer-reviewed formalization venues (ITP/CPP/JFR).
- **Likely case:** All 5 Lean suites compile cleanly across all 6 kernels, all 12 wild paths are audited with concrete counterexamples/seam theorems, and a publication-grade Tectonic PDF white paper ships with zero unverified claims.
- **Cost of failure:** Compute time only (0 monetary cost); pessimistic effort estimate 2–3× optimistic still fits cleanly within this autonomous `/goal` run.
- **Decision (2026-11-23):** **GO** — strict epistemic honesty enforced (zero false claim of resolving `P vs NP`).
