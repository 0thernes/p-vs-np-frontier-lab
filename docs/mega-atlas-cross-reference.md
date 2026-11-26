<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Cross-Reference Against the Unsolved Problems Mega-Atlas V2 (`1,900` Problems)

**Audit date:** 2026-11-25  
**Catalog:** [`0thernes/unsolved-problems-mega-atlas`](https://github.com/0thernes/unsolved-problems-mega-atlas) (`1,900` curated problems across 8 Pillars & 28 Superdomains)  
**Archive Entry:** `0TH-2026-013` in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive)

## Executive Verdict

- **Grand Mega-Atlas problems completely solved by `p-vs-np-frontier-lab`:** **`0 / 1,900`**.
- **Exact contribution:** Machine-checked Lean 4.35.0 formalization of classical **complexity-theoretic barriers and structural phase transitions** (`C1`–`C14`, 6 independent kernels) plus **exact computational falsifiers** (`E1`–`E10`) refuting four aggressive $\mathrm{P}=\mathrm{NP}$ heuristics, directly illuminating why naive attacks fail on `CS-001`, `CS-005`, `CS-010`, `CS-012`, and `QM-011`.

| Mega-Atlas ID | Problem Title | Verdict | What Is Proved vs. What Remains Open |
|---|---|---|---|
| **`CS-001`** | P versus NP Problem | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** Baker–Gill–Solovay dual relativization (`C1`–`C2`), Razborov–Rudich natural proofs (`C3`–`C5`), Schaefer polymorphism rigidity (`C8`–`C9`), and 4 heuristic falsifiers (`E7`–`E9`). **Still Open:** $\mathrm{P} \stackrel{?}{=} \mathrm{NP}$. |
| **`CS-010`** | Super-Linear Explicit Boolean Circuit Lower Bounds & Natural Proofs Barrier | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** Natural proofs PRF breaker (`C3`–`C5`), tight Markov–Fischer negation threshold (`C10`–`C11`), multiplicative complexity degree bound (`C12`), plus exact CaDiCaL MC gaps (`E3`–`E4`). **Still Open:** Super-linear unrestricted Boolean circuit lower bounds & exact $\mathrm{MC}(\mathrm{CLIQUE}_{4,3}) \in \{5,6\}$. |
| **`CS-012`** | Valiant's Algebraic Complexity Conjecture: VP vs. VNP (Permanent vs. Determinant) | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** Characteristic-2 $\mathrm{Perm}_n \equiv \det_n \pmod 2$ collapse & universal $p \ge 3$ witness $W_n$ (`C13`), plus exact rational Mignon–Ressayre Hessian ranks (`E10`). **Still Open:** $\mathrm{VP} \neq \mathrm{VNP}$ over characteristic $\neq 2$. |
| **`CS-005`** | P vs. PSPACE, L vs. P & NC vs. P (Catalytic Space) | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** Exact reversible zero-workspace $d$-fold catalytic multilinear product in $3\cdot 4^{d-1}$ ops (`C14`), directly motivating the open-question breakthrough in `0TH-2026-010` (`catalytic-register-frontiers`). **Still Open:** $\mathrm{L} \neq \mathrm{P}$, $\mathrm{P} \neq \mathrm{PSPACE}$. |
| **`QM-011`** | Quantum Contextuality & Ontological Models | **`RELATED_BRIDGE / STILL OPEN`** | **Proved (Lean 4.35.0):** Odd-cycle ($C_{2k+3}$) and Mermin–Peres ($3\times 3$) parity sheaves are maximally contextual while sitting inside $\mathrm{XOR\text{-}SAT} \subseteq \mathrm{P}$ (`C6`–`C7`), proving contextuality alone does not imply NP-hardness. **Still Open:** General Spekkens contextuality & continuous-variable foundations. |
