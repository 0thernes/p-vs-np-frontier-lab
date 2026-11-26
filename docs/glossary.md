<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Glossary (`docs/glossary.md`)

- **Baker–Gill–Solovay Barrier (`C2`):** Existence of computable oracles $A, B$ with $\mathrm{P}^A = \mathrm{NP}^A$ and $\mathrm{P}^B \neq \mathrm{NP}^B$ (`lean/PVsNP/Relativization.lean`).
- **Catalytic Zero-Workspace Program (`C14`):** Reversible straight-line arithmetic program computing $\prod_{i=1}^d x_i$ while restoring all $d$ arbitrary catalyst registers bit-for-bit (`lean/PVsNP/CatalyticAlgebra.lean`).
- **Multiplicative Complexity (`C12`):** Minimum number of AND gates over $\{\oplus, \land, 1\}$ required to compute a Boolean function (`lean/PVsNP/CircuitPhaseTransition.lean`).
- **Natural Proof (`C3`–`C5`):** Large, constructive combinatorial property useful against a circuit class (`lean/PVsNP/NaturalProofs.lean`).
- **Palomar Comparator:** Lean 4.35.0 built-in `lake comparator --paranoid` multi-kernel verifier comparing isolated `PalomarChallenge.lean` statements against sorry-free `PalomarSolution.lean` proofs across 6 kernels.
- **Polymorphism Rigidity (`C8`–`C9`):** Property of a CSP template whose polymorphisms of every finite arity are strictly coordinate projections (`lean/PVsNP/SheafPolymorphism.lean`).
- **Ten Finding Classes (Build Standard `R7`):** `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot` (see `.github/labels.tsv`).
