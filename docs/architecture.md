<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Proof Architecture (`docs/architecture.md`)

## 1. Layered Verification Pipeline

```text
  [lean/PVsNP/*.lean (9 core modules, zero Mathlib)]
        │
        ├──▶ lean/Challenge.lean (14 human-auditable Prop statements, 0 proofs)
        ├──▶ lean/Solution.lean  (witnesses proving C1..C14 + AllFrontierTheoremsStmt)
        └──▶ lean/VerifyAxioms.lean ──▶ results/lean_axioms.txt
                  │
                  ├──▶ leanchecker / leanchecker-paranoid (.olean replay)
                  └──▶ leanexport (NDJSON) ──▶ con-leche --verified
                                           ──▶ con-ron   --verified
                                           ──▶ nanoda_bin (strict 3 axioms)

  [experiments/exp1..exp5.py] ──▶ results/*.json ──▶ tests/test_all.py (pytest)
                                        │
                                        └──▶ scripts/make_figures.py ──▶ paper/figures/*.pdf
                                                                               │
  [paper/main.tex] ◄───────────────────────────────────────────────────────────┘
        │
        └──▶ Tectonic ──▶ dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf
                      ──▶ dist/arxiv_submission.tar.gz ──▶ MANIFEST.sha256
```

## 2. Lean Module Dependency Graph

- `PVsNP.Basic` — constructive `allBitstrings`, pigeonhole, Cantor pairing.
- `PVsNP.OTM` — explicit 4-tape Oracle Turing Machine, `encodeOTM`/`decode_encodeOTM`, `InP`, `InNP`, `p_subset_np` (`C1`).
  - `PVsNP.RelativizationSep` — stagewise diagonalization oracle $B$ (`bgs_oracle_separation`).
  - `PVsNP.RelativizationCol` — canonical bounded-halting collapse oracle $A$ (`bgs_oracle_collapse`).
  - `PVsNP.Relativization` — unified `baker_gill_solovay` (`C2`).
- `PVsNP.NaturalProofs` — counting step of the natural-proofs argument with an exact integer bound (`C3`), integer pigeonhole telescoping bound (`C4`), `nonConstantProp` largeness witness (`C5`).
- `PVsNP.SheafPolymorphism` — minimal unsatisfiability of odd-cycle XOR systems on $2k+1$ variables (`C6`) and of the Mermin–Peres system (`C7`), four polymorphism preservation facts (`C8`), all-arity projection-only rigidity of $\{R_{000}, R_{111}\}$ via finite principal ultrafilters (`C9`).
- `PVsNP.CircuitPhaseTransition` — Markov $k$-NOT lower bound and upper bound for $n = 2^k - 1$ (`C10`), dual-rail k-NOT compilation without size bound (`C11`), multiplicative complexity subset-product degree bound (`C12`), char-2 permanent/determinant collapse + $W_n = \mathrm{diag}(I_{n-2}, J_2)$ universal $p \ge 3$ witness (`C13`).
- `PVsNP.CatalyticAlgebra` — `invertProg` undoes well-formed straight-line register programs, and a recursive program of $3\cdot 4^{d-1} - 2$ instructions adds a product of program constants while restoring all other registers (`C14`).
- `Challenge` / `Solution` / `VerifyAxioms` — public specification-vs-proof interface and axiom audit.

## 3. Architectural Decision Records
- `docs/adr/0001-zero-mathlib-six-kernel-lean.md` — rationale for zero-Mathlib Lean 4.35 `module` design and multi-kernel replay.
- `docs/adr/0002-epistemic-scope-and-identity.md` — resolution of epistemic boundaries, independent-researcher identity, and dual Apache-2.0 / CC-BY-4.0 licensing.
