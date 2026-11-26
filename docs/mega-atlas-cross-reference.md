<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Cross-Reference Against the Unsolved Problems Mega-Atlas V2 (`1,900` Problems)

**Audit date:** 2026-11-25  
**Catalog:** [`0thernes/unsolved-problems-mega-atlas`](https://github.com/0thernes/unsolved-problems-mega-atlas) (`1,900` curated problems across 8 Pillars & 28 Superdomains)  
**Archive Entry:** `0TH-2026-013` in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive)

## Executive Verdict

- **Grand Mega-Atlas problems completely solved by `p-vs-np-frontier-lab`:** **`0 / 1,900`**.
- **Exact contribution:** Machine-checked Lean 4.35.0 formalization of known results (`C1`–`C14`: the Baker–Gill–Solovay theorem, the counting step of natural proofs, and twelve classical supporting lemmas; six kernel checks with five checker implementations) plus exact computations (`E1`–`E10`), including three exact counterexamples and one numerical illustration against four illustrative SAT heuristics. No problem in the list below is advanced.

| Mega-Atlas ID | Problem Title | Verdict | What Is Proved vs. What Remains Open |
|---|---|---|---|
| **`CS-001`** | P versus NP Problem | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** the Baker–Gill–Solovay theorem in an explicit oracle Turing machine model (`C1`–`C2`), the counting step of the natural-proofs argument (`C3`–`C5`), and polymorphism facts including projection-only rigidity of $\{R_{000}, R_{111}\}$ (`C8`–`C9`). **Computed:** counterexamples to illustrative heuristics (`E7`–`E9`). **Still Open:** $\mathrm{P} \stackrel{?}{=} \mathrm{NP}$. |
| **`CS-010`** | Super-Linear Explicit Boolean Circuit Lower Bounds & Natural Proofs Barrier | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** natural-proofs counting step (`C3`–`C5`), Markov's negation bound and a k-NOT compilation without size bound (`C10`–`C11`), AND-count versus $\mathbb{F}_2$-degree (`C12`). **Computed:** CaDiCaL MC values (`E3`–`E4`) that reproduce published classifications (Turan–Peralta; Calik–Turan–Peralta 2019). **Still Open:** super-linear unrestricted Boolean circuit lower bounds. |
| **`CS-012`** | Valiant's Algebraic Complexity Conjecture: VP vs. VNP (Permanent vs. Determinant) | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** $\mathrm{Perm}_n \equiv \det_n \pmod 2$ and a witness $W_n$ with permanent 2 and determinant 0 (`C13`). **Computed:** exact rational Mignon–Ressayre Hessian ranks (`E10`). **Still Open:** $\mathrm{VP} \neq \mathrm{VNP}$ over characteristic $\neq 2$. |
| **`CS-005`** | P vs. PSPACE, L vs. P & NC vs. P (Catalytic Space) | **`BARRIER_FORMALIZATION / STILL OPEN`** | **Proved (Lean 4.35.0):** reversibility of straight-line register programs and one recursive program of $3\cdot 4^{d-1} - 2$ instructions that adds a product of program constants while restoring all other registers (`C14`). No space bound is formalized; Ben-Or and Cleve (1992) is closer prior work. **Still Open:** $\mathrm{L} \neq \mathrm{P}$, $\mathrm{P} \neq \mathrm{PSPACE}$. |
| **`QM-011`** | Quantum Contextuality & Ontological Models | **`RELATED_BRIDGE / STILL OPEN`** | **Proved (Lean 4.35.0):** odd-cycle XOR systems on $2k+1$ variables and the Mermin–Peres parity system are minimally unsatisfiable while lying in $\mathrm{XOR\text{-}SAT} \subseteq \mathrm{P}$ (`C6`–`C7`). The sheaf-theoretic notion of contextuality is not formalized. **Still Open:** General Spekkens contextuality & continuous-variable foundations. |
