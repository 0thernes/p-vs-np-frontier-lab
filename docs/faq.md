<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`)

### 1. Does this repository claim to prove P = NP or P != NP?
**No.** P vs. NP (`CS-001`) remains **completely open**. See [CLAIMS.md](../CLAIMS.md) and [LIMITATIONS.md](../LIMITATIONS.md).

### 2. What is actually proved in Lean 4?
Fourteen unconditional theorems (`C1`–`C14`, 8,078 lines, zero Mathlib, zero `sorry`) covering Baker–Gill–Solovay dual relativization (`C1`–`C2`), Razborov–Rudich exact-integer natural proofs (`C3`–`C5`), odd-cycle & Mermin–Peres maximal contextuality (`C6`–`C7`), Schaefer tractable polymorphisms & all-arity `{R000, R111}` inclusion-minimal rigidity (`C8`–`C9`), Markov–Fischer bounded negation (`C10`–`C11`), multiplicative complexity degree lower bounds (`C12`), char-2 permanent–determinant collapse vs. mod-$p$ separation (`C13`), and reversible zero-workspace catalytic multilinear multiplication (`C14`).

### 3. How can I verify the Lean proofs in under a minute?
Install Lean `v4.35.0` via `elan` (no Mathlib download required), run `cd lean && lake build && lake env lean VerifyAxioms.lean`, and on Linux run `lake check --paranoid && lake comparator --config comparator.json --paranoid`.

### 4. Why not rely on Mathlib?
Zero Mathlib keeps the trusted computing base tiny and guarantees sub-minute offline rebuilds and fast 6-kernel verification across `lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, and `con-ron` (see [ADR 0001](adr/0001-zero-mathlib-six-kernel-lean.md)).

### 5. Can I contribute or report a fidelity flaw?
Yes—open an issue via `.github/ISSUE_TEMPLATE/` classified with one of the 10 Build Standard classes (`docs/glossary.md`).
