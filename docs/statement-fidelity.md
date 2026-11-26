<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Statement-Fidelity Audit (`docs/statement-fidelity.md`)

Maps every formalized theorem in `lean/Challenge.lean` and `lean/PalomarChallenge.lean` against its textbook complexity-theoretic literature anchor (Defensible Independent AI Research Playbook v1.3, item #10).

| ID | Lean Declaration (`Challenge.lean`) | Literature Anchor | Fidelity & Boundary Notes | Status |
|---|---|---|---|---|
| `C1` | `PSubsetNPStmt` | Textbook $\mathrm{P}^O \subseteq \mathrm{NP}^O$ | Explicit 4-tape Oracle Turing Machine model in `PVsNP.OTM`; zero-witness deterministic simulation. | **Match** |
| `C2` | `BakerGillSolovayStmt` | Baker, Gill & Solovay, *SIAM J. Comput.* 4(4) (1975) | Constructs explicit computable collapse oracle $A$ (padded universal evaluator) and diagonalization separation oracle $B$. | **Match** |
| `C3` | `NaturalProofBreaksPRFStmt` | Razborov & Rudich, *JCSS* 55(1) (1997) | Exact cross-multiplied integer distinguishing bound for arbitrary fixed $n, k, \text{numer}/\text{denom}$ avoiding floating-point probability; asymptotic PRF assumption explicitly separated in `LIMITATIONS.md`. | **Match (finite-$n$ exact)** |
| `C4` | `HybridTelescopingStmt` | Goldreich–Goldwasser–Micali (1986) hybrid argument | Exact integer telescoping triangle inequality on any sequence $a_0, \dots, a_m \in \mathbb{Z}$. | **Match** |
| `C5` | `NaturalProofNonvacuousStmt` | Non-vacuity witness for `IsLarge` / `IsUsefulAgainst` | Exhibits `nonConstantProp` with exact density $\ge 1/2$ for all $n \ge 1$ ruling out vacuous definitions. | **Match** |
| `C6` | `OddCycleContextualStmt` | Abramsky–Brandenburger (2011) sheaf contextuality | Proves every odd cycle $C_{2k+3}$ parity system is strongly (maximally) contextual while sitting in $\mathrm{XOR\text{-}2SAT} \subseteq \mathrm{P}$. | **Match** |
| `C7` | `MerminPeresContextualStmt` | Peres (1990), Mermin (1993) $3\times 3$ magic square | Proves maximal contextuality of the 6-equation 9-variable Mermin–Peres parity system inside $\mathrm{P}$. | **Match** |
| `C8` | `TractablePolymorphismsStmt` | Schaefer (1978), Jeavons (1998) | Proves exact polymorphism preservation for Maltsev XOR, Horn AND, Dual-Horn OR, and 2-SAT Majority. | **Match** |
| `C9` | `Monotone3SATRigidStmt` | Schaefer (1978) / Post lattice rigidity | Proves for ALL finite arities $k \ge 1$ that $\{R_{000}, R_{111}\}$ admits only projections and is inclusion-minimal; NP-hardness deduction remains conditional on $\mathrm{P} \neq \mathrm{NP}$. | **Match** |
| `C10` | `MarkovInverterTightStmt` | Markov (1957) bounded-negation theorem | Proves both lower bound ($2^r \le n \Rightarrow$ impossible with $\le r$ NOTs) and constructive upper bound ($k$ NOTs invert $2^k-1$ bits). | **Match** |
| `C11` | `FischerReductionStmt` | Fischer (1975) negation-limited compilation | Proves exact dual-rail De Morgan simulation of arbitrary circuits on $2^k-1$ bits with exactly $k$ NOT gates. | **Match** |
| `C12` | `MultiplicativeComplexityStmt` | Schnorr (1988), Boyar–Peralta (2000) | Proves $\deg_{\mathbb{F}_2}(f) \le \mathrm{MC}(f) + 1$ and $\mathrm{MC}(\mathrm{AND}_n) \ge n - 1$ over $\{\oplus, \land, 1\}$. | **Match** |
| `C13` | `PermDetChar2Stmt` | Valiant (1979) characteristic-2 collapse | Proves $\mathrm{Perm}_n(A) \equiv \det_n(A) \pmod 2$ for all $A \in \mathbb{Z}^{n\times n}$ and explicit separation witness $W_n$ mod every $p \ge 3$. | **Match** |
| `C14` | `CatalyticAlgebraStmt` | Buhrman et al. (2014) catalytic straight-line algebra | Proves exact bijective reversibility (`invertProg`) and $d$-fold zero-workspace product in exactly $3\cdot 4^{d-1}$ operations. | **Match** |
