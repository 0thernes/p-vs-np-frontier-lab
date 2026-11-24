<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# P vs. NP Frontier & Barrier Anatomy Lab (`p-vs-np-frontier-lab`)

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID: [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648))  
**Version:** `1.0.0` · **License:** Dual — `Apache-2.0` (code, Lean proofs, scripts) + `CC-BY-4.0` (paper, docs, figures)

> ### Epistemic Scope Boundary (Explicit Non-Claim)
> **$\mathrm{P}$ vs. $\mathrm{NP}$ remains completely open.** Nothing in this repository claims a proof of $\mathrm{P} = \mathrm{NP}$ or $\mathrm{P} \neq \mathrm{NP}$.  
> This repository delivers:
> 1. **Tier 1 (Machine-Checked Lean 4.35 Theorems `C1`–`C14`):** 14 unconditional complexity-barrier, algebraic-rigidity, circuit phase-transition, and zero-workspace catalytic theorems (8,078 lines across 13 zero-Mathlib `module` files) verified across **6 kernel checks (5 independent implementations)** with zero `sorry`s and zero custom axioms.
> 2. **Tier 2 (Exact-Arithmetic & SAT-Certified Experiments):** 4 exact integer/rational/$\mathbb{F}_2$/CaDiCaL 2.1.2 computational experiments + 10/10 `pytest` verification suite (including an exhaustive brute-force SAT-encoder audit on $n=3$).
> 3. **Tier 3 (Explicitly Tagged `numerical_approximation`):** Adaptive `float64` RK45 ODE benchmark for Attack A (CTDS) contrasting planted SAT convergence against exact UNSAT exponential Lagrange energy blowup.
> 4. **Tier 4 (Publication-Grade AMS-LaTeX White Paper):** 15-page frozen PDF ([`dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`](dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf)) and clean-room-tested arXiv source tarball ([`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)).

---

## 5-Second Verbatim Axiom & Kernel Proof Check

Verify every single theorem in `lean/Solution.lean` from scratch (requires Lean `v4.35.0`, zero Mathlib download):

```bash
cd lean
lake build
lake env lean VerifyAxioms.lean
```

**Verbatim output (`results/lean_axioms.txt`):**

```text
'Solution.prove_p_subset_np' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_natural_proof_breaks_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_hybrid_telescoping' depends on axioms: [propext, Quot.sound]
'Solution.prove_natural_proof_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_odd_cycle_contextual' depends on axioms: [propext, Quot.sound]
'Solution.prove_mermin_peres_contextual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_tractable_polymorphisms' depends on axioms: [propext]
'Solution.prove_monotone_3sat_rigid' depends on axioms: [propext, Quot.sound]
'Solution.prove_markov_inverter_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_fischer_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_multiplicative_complexity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_perm_det_char2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.prove_catalytic_algebra' depends on axioms: [propext, Quot.sound]
'Solution.prove_all_frontier_theorems' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Multi-Kernel Verification Ledger (`results/six_kernel_audit.txt`)

| Checker / Kernel | Independent Implementation | Exit | Verdict |
|---|---|---|---|
| `lean.exe` + `VerifyAxioms.lean` | C++ reference kernel | `0` | 16/16 jobs, 0 warnings, 3 standard axioms |
| `leanchecker.exe Solution` | C++ external `.olean` replay | `0` | Accepted full import closure |
| `leanchecker-paranoid.exe Solution` | C++ paranoid `.olean` replay | `0` | Full paranoid definitional checks passed |
| `con-leche.exe --verified` | Verified Lean-in-Lean set-model kernel | `0` | `accepted 3982 declarations (--verified)` |
| `con-ron.exe --verified` | Aeneas-verified Rust arena kernel | `0` | `accepted 3982 declarations (--verified)` |
| `nanoda_bin.exe` 0.4.19 | Independent Rust external typechecker | `0` | `Checked 4319 declarations`, 0 errors (`unpermitted_axiom_hard_error=true`) |

> **Honest Upstream Toolchain Note:** On Windows `leanprover/lean4:v4.35.0`, the bundled `lean4lean.exe` fails with `incompatible header` even on Lean's own stdlib `Init.Prelude.olean`, and `lake check` requires Linux `bwrap`/`git`. See `results/six_kernel_audit.txt` and `LIMITATIONS.md` for full diagnostics; Linux CI (`.github/workflows/ci.yml`) invokes `lake check` natively.

---

## Statement-Fidelity Table (`lean/Challenge.lean` ↔ `lean/Solution.lean`)

| ID | Lean Module | Challenge Statement / Solution Proof | Mathematical Result |
|---|---|---|---|
| `C1` | `PVsNP.OTM` | `PSubsetNPStmt` / `prove_p_subset_np` | $\forall O,\; \mathrm{P}^O \subseteq \mathrm{NP}^O$ (explicit 4-tape OTM) |
| `C2` | `PVsNP.Relativization` | `BakerGillSolovayStmt` / `prove_baker_gill_solovay` | $\exists A,B,\; \mathrm{P}^A = \mathrm{NP}^A \land \mathrm{P}^B \neq \mathrm{NP}^B$ |
| `C3` | `PVsNP.NaturalProofs` | `NaturalProofBreaksPRFStmt` / `prove_natural_proof_breaks_prf` | Exact cross-multiplied $\mathbb{Z}$ Razborov–Rudich PRF break |
| `C4` | `PVsNP.NaturalProofs` | `HybridTelescopingStmt` / `prove_hybrid_telescoping` | Exact $\mathbb{Z}$ hybrid telescoping triangle inequality |
| `C5` | `PVsNP.NaturalProofs` | `NaturalProofNonVacuousStmt` / `prove_natural_proof_nonvacuous` | `nonConstantProp` density $\ge 1/2$ for all $n \ge 1$ |
| `C6` | `PVsNP.SheafPolymorphism` | `OddCycleContextualStmt` / `prove_odd_cycle_contextual` | Odd cycles $C_{2k+3}$ maximally contextual for all $k$ |
| `C7` | `PVsNP.SheafPolymorphism` | `MerminPeresContextualStmt` / `prove_mermin_peres_contextual` | Mermin–Peres $3\times 3$ magic square maximally contextual |
| `C8` | `PVsNP.SheafPolymorphism` | `TractablePolymorphismsStmt` / `prove_tractable_polymorphisms` | Maltsev XOR, Horn AND, Dual-Horn OR, 2-SAT Majority |
| `C9` | `PVsNP.SheafPolymorphism` | `Monotone3SATRigidStmt` / `prove_monotone_3sat_rigid` | $\forall k \ge 1$, $\{R_{000}, R_{111}\}$ inclusion-minimal rigid |
| `C10` | `PVsNP.CircuitPhaseTransition` | `MarkovInverterTightStmt` / `prove_markov_inverter_tight` | $k$ NOT gates invert $n$ bits $\iff n \le 2^k - 1$ |
| `C11` | `PVsNP.CircuitPhaseTransition` | `FischerReductionStmt` / `prove_fischer_reduction` | Universal dual-rail compilation to $\le k$ NOT gates |
| `C12` | `PVsNP.CircuitPhaseTransition` | `MultiplicativeComplexityStmt` / `prove_multiplicative_complexity` | $\deg_{\mathbb{F}_2}(f) \le k + 1$ and $\mathrm{MC}(\mathrm{AND}_n) \ge n - 1$ |
| `C13` | `PVsNP.CircuitPhaseTransition` | `PermDetChar2Stmt` / `prove_perm_det_char2` | $\mathrm{Perm}_n \equiv \det_n \pmod 2$ and $W_n$ separating mod all $p \ge 3$ |
| `C14` | `PVsNP.CatalyticAlgebra` | `CatalyticAlgebraStmt` / `prove_catalytic_algebra` | Bijective reversibility & exact $3\cdot 4^{d-1}$ $d$-fold zero-workspace mul |

---

## Repository Map

```text
p-vs-np-frontier-lab/
├── lean/                         # Zero-Mathlib Lean 4.35.0 library (13 files, 8,078 lines)
│   ├── Challenge.lean            # Human-auditable specifications C1-C14 (zero proofs)
│   ├── Solution.lean             # Proof witnesses + AllFrontierTheoremsStmt
│   ├── VerifyAxioms.lean         # Verbatim #print axioms audit script
│   ├── formalization.yaml        # Machine-readable claim-to-Lean ledger
│   └── PVsNP/                    # 9 core modules (OTM, BGS, NaturalProofs, Sheaf, Circuits, Catalytic)
├── experiments/                  # 5 computational discovery & falsification scripts
├── results/                      # Verified JSON outputs, lean_axioms.txt, six_kernel_audit.txt
├── tests/test_all.py             # 10-test verification & brute-force SAT-encoder audit suite
├── scripts/
│   ├── make_figures.py           # Generates 4 vector PDF figures in paper/figures/
│   └── run_all.ps1               # End-to-end Windows orchestrator (-Task all|lean|tests|...)
├── paper/
│   ├── main.tex                  # AMS-LaTeX white paper (zero Overfull/Underfull hboxes)
│   └── figures/                  # 4 colorblind-safe vector PDF figures
├── dist/
│   ├── Donahue_2026_p_vs_np_barrier_anatomy.pdf
│   └── arxiv_submission.tar.gz   # Clean-room-verified standalone arXiv package
├── docs/                         # Plans, red-team, ADRs, architecture, threat model, 10-pass review
├── CLAIMS.md                     # Complete claim-to-evidence ledger (C1-C14, E1-E10, O1-O3)
├── LIMITATIONS.md                # Honest boundaries, timeouts, float64 and toolchain notes
├── REPLICATION.md                # Step-by-step reproduction guide (Windows & Linux)
├── MANIFEST.sha256               # Cryptographic SHA-256 provenance manifest
└── repo.yaml                     # Build Standard v1.1.0 machine-readable repo card
```

## Quick-Start Reproduction

Run the entire verification pipeline (Lean rebuild + axiom audit + `pytest` + figure generation + Tectonic PDF build + SHA-256 check):

```powershell
pwsh -File scripts/run_all.ps1 -Task all
```

See [`REPLICATION.md`](REPLICATION.md) for Linux commands and individual task flags.
