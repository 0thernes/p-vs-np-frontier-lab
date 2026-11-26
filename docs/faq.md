<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`)

### 1. Does this repository claim to prove P = NP or P != NP?
**No.** P vs. NP (`CS-001`) remains **completely open**. See [CLAIMS.md](../CLAIMS.md) and [LIMITATIONS.md](../LIMITATIONS.md).

### 2. What is actually proved in Lean 4?
Fourteen statements of known mathematics (`C1`–`C14`; 17 Lean files, 8,266 lines at v1.2.0; zero Mathlib; zero `sorry` in proof modules): the Baker–Gill–Solovay theorem in an explicit oracle Turing machine model (`C1`–`C2`), the counting step of the Razborov–Rudich natural-proofs argument (`C3`–`C5`), minimal unsatisfiability of odd-cycle and Mermin–Peres parity systems (`C6`–`C7`), four polymorphism preservation facts and projection-only rigidity of `{R000, R111}` (`C8`–`C9`), Markov's negation bound and a k-NOT compilation without size bound (`C10`–`C11`), AND-count versus $\mathbb{F}_2$-degree (`C12`), permanent = determinant mod 2 with a mod-$p$ witness (`C13`), and reversibility of straight-line register programs (`C14`). Only `C2` is a barrier theorem in full. See [CLAIMS.md](../CLAIMS.md) for exact statements and prior work.

### 3. How can I verify the Lean proofs in under a minute?
Install Lean `v4.35.0` via `elan` (no Mathlib download required), run `cd lean && lake build && lake env lean VerifyAxioms.lean`, and on Linux run `lake check --paranoid && lake comparator --config comparator.json --paranoid`.

### 4. Why not rely on Mathlib?
Zero Mathlib keeps the trusted computing base small and allows fast offline rebuilds and six kernel checks with five checker implementations (the Lean reference kernel in default and paranoid mode, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`; see [ADR 0001](adr/0001-zero-mathlib-six-kernel-lean.md)).

### 5. Can I contribute or report a fidelity flaw?
Yes—open an issue via `.github/ISSUE_TEMPLATE/` classified with one of the 10 Build Standard classes (`docs/glossary.md`).
