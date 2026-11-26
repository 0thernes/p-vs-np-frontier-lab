<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Glossary (`docs/glossary.md`)

- **Baker–Gill–Solovay Barrier (`C2`):** Existence of explicitly defined oracles $A, B$ with $\mathrm{P}^A = \mathrm{NP}^A$ and $\mathrm{P}^B \neq \mathrm{NP}^B$ in this repository's oracle Turing machine model (`lean/PVsNP/Relativization.lean`).
- **Catalytic Zero-Workspace Program (`C14`):** Reversible straight-line register program of $3\cdot 4^{d-1} - 2$ instructions that adds $\pm \prod_{i=1}^d x_i$, for integers $x_i$ fixed in the program, to one register and restores every other register whatever its initial contents (`lean/PVsNP/CatalyticAlgebra.lean`). No catalytic-space bound is formalized.
- **Multiplicative Complexity (`C12`):** Minimum number of AND gates over $\{\oplus, \land, 1\}$ required to compute a Boolean function (`lean/PVsNP/CircuitPhaseTransition.lean`).
- **Natural Proof (`C3`–`C5`):** Large, constructive combinatorial property useful against a circuit class. The Lean code (`lean/PVsNP/NaturalProofs.lean`) formalizes largeness and usefulness for an arbitrary property; constructivity and the circuit class are not formalized.
- **Palomar Comparator:** Lean 4.35.0 built-in `lake comparator --paranoid` multi-kernel verifier comparing isolated `PalomarChallenge.lean` statements (15 intentional `sorry` stubs) against sorry-free `PalomarSolution.lean` proofs with six kernel checks (five checker implementations).
- **Polymorphism Rigidity (`C8`–`C9`):** Property of a CSP template whose polymorphisms of every finite arity are strictly coordinate projections (`lean/PVsNP/SheafPolymorphism.lean`).
- **Ten Finding Classes (Build Standard `R7`):** `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot` (see `.github/labels.tsv`).
