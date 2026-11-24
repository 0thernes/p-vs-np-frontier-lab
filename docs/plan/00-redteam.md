# P0 Red-Team & Kill Criteria (`p-vs-np-frontier-lab`)

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

## Five Riskiest Assumptions (P0.06)

| # | Assumption | Tag | Failure Mode | Planned Test / Mitigation |
|---|---|---|---|---|
| 1 | The Baker–Gill–Solovay 3-tape Oracle Turing Machine formalization is faithful to the textbook model (not vacuous or weakened). | **feasibility / validity** | Defining `OracleP` too weakly (e.g. omitting polynomial step-counting or oracle query construction) makes `P^A = NP^A` or `P^B ≠ NP^B` trivial. | Isolate all definitions in `Challenge.lean`, prove explicit non-vacuity witnesses (`P^O ⊆ NP^O`, concrete OTMs for parity, constants, `unaryLang B`, explicit OTM encoding/decoding), and audit line-by-line in the Statement-Fidelity Table. |
| 2 | All 6 independent Lean 4.35.0 kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) accept the compiled modules on Windows. | **feasibility** | Windows path handling (`[Vibe Coded (AI)]` brackets) or bubblewrap absence could break `lake check --paranoid` or `lake comparator`. | Test `leanexport` + every individual kernel binary (`leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) directly AND test `lake check` / `lake comparator`; record exact exit codes and logs. |
| 3 | SAT-based exact Multiplicative Complexity synthesis (`CaDiCaL 2.1.2`) terminates quickly enough on $n=4,5,6$ functions to yield genuine exact lower bounds ($\mathrm{MC}(f) > \deg(f) - 1$). | **feasibility** | Exact circuit synthesis CNF can blow up exponentially at $k \ge 5$ AND gates. | Add symmetry-breaking clauses (topological ordering, no duplicate/trivial gates, canonical variable symmetry) and hard per-query timeouts; verify every SAT solution by independent Python circuit evaluation and UNSAT bounds on small $n$ by brute-force cross-check. |
| 4 | Continuous-time dynamical SAT solver (CTDS) numerical integration could introduce floating-point artifacts. | **validity** | Claiming exact exponential growth from float64 ODE integration violates the Playbook's "Float Illusion" guardrail. | Label CTDS ODE integration explicitly as `numerical-approximation`, verify with step-size refinement / adaptive tolerances, and pair with exact discrete Lyapunov / analytical lower-bound analysis and exact rational LP (`fractions.Fraction`) for all exact-claim rows. |
| 5 | AI-assisted proof/paper production could inadvertently overclaim novelty or trigger Zenodo/arXiv policy conflicts. | **ethics / viability** | Claiming novelty for classical theorems (Baker–Gill–Solovay 1975, Markov 1957, Fischer 1974, Razborov–Rudich 1994, Schaefer 1978, Boyar–Peralta–Pochuev 2000) or asserting unformed `0thernes LLC`. | Explicitly cite every classical primary source, distinguish classical formalized theorems from newly synthesized computational/structural findings, tag every claim in `CLAIMS.md`, and list `Alexander S. Donahue (independent researcher)` with honest CRediT + AI-tool disclosure. |

## Kill / Pivot Criteria (P0.07)

1. **Formal soundness gate (2026-11-23):** If ANY Lean theorem requires `sorry`, `admit`, `native_decide`, or a custom axiom — **KILL that theorem** (never ship an incomplete proof).
2. **Kernel rejection gate (2026-11-23):** If ANY of the 6 independent kernels rejects an exported module — **STOP and fix** until all 6 accept with exit code 0 (or log as a classified `bug`/`problem` and withhold release).
3. **Statement-fidelity gate (2026-11-23):** If adversarial definition review shows any headline theorem is vacuous (e.g. an empty hypothesis class) or admits a trivial proof of a false variant — **REFACTOR definitions and re-prove** before proceeding to paper compilation.
4. **Claim-honesty gate (2026-11-23):** Any sentence in `README.md` or `paper/main.tex` that exceeds its `CLAIMS.md` tag blocks release until softened or backed by reproducible evidence.
