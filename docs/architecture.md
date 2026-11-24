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
- `PVsNP.NaturalProofs` — exact cross-multiplied $\mathbb{Z}$ PRF breaker (`C3`), hybrid telescoping (`C4`), `nonConstantProp` largeness witness (`C5`).
- `PVsNP.SheafPolymorphism` — odd cycles $C_{2k+3}$ (`C6`), Mermin–Peres (`C7`), Schaefer polymorphisms (`C8`), all-arity monotone 3-SAT inclusion-minimal rigidity via finite principal ultrafilters (`C9`).
- `PVsNP.CircuitPhaseTransition` — Markov $k$-NOT lower/upper bounds (`C10`), Fischer dual-rail De Morgan compiler (`C11`), multiplicative complexity subset-product degree bound (`C12`), char-2 permanent/determinant collapse + $W_n = \mathrm{diag}(I_{n-2}, J_2)$ universal $p \ge 3$ witness (`C13`).
- `PVsNP.CatalyticAlgebra` — Landauer bijective `invertProg` + arbitrary-degree $d$-fold zero-workspace catalytic multilinear product restoring all $d$ arbitrary catalysts in $3\cdot 4^{d-1}$ ops (`C14`).
- `Challenge` / `Solution` / `VerifyAxioms` — public specification-vs-proof interface and axiom audit.

## 3. Architectural Decision Records
- `docs/adr/0001-zero-mathlib-six-kernel-lean.md` — rationale for zero-Mathlib Lean 4.35 `module` design and multi-kernel replay.
- `docs/adr/0002-epistemic-scope-and-identity.md` — resolution of epistemic boundaries, independent-researcher identity, and dual Apache-2.0 / CC-BY-4.0 licensing.
