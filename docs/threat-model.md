<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Epistemic & Engineering Threat Model (`docs/threat-model.md`)

Because this repository targets a Millennium Prize problem with AI assistance, threats are primarily **epistemic integrity, soundness, and reproducibility threats** rather than network-service exploits.

| Threat ID | Threat Vector | Impact | Control / Mitigation | Verification Check |
|---|---|---|---|---|
| `TM-01` | **Hidden unsoundness in Lean proofs** (`sorry`, `admit`, `native_decide`, custom `axiom`, `@[extern]`) | Invalid mathematical claims | Zero-Mathlib `module` codebase; comment-stripped regex scan; `VerifyAxioms.lean`; `nanoda_bin` with `unpermitted_axiom_hard_error=true` | `test_lean_zero_forbidden_tokens_and_module_headers`, `test_lean_axioms_strictly_standard`, `results/six_kernel_audit.txt` |
| `TM-02` | **Single-kernel implementation bug** | Soundness hole in reference C++ kernel | Independent replay across 6 kernel checks / 5 distinct codebases (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) | `results/six_kernel_audit.txt` |
| `TM-03` | **Statement weakening / proxy mismatch** | Proving trivialized theorem while paper claims textbook statement | Isolated 145-line proof-free `lean/Challenge.lean` + Statement-Fidelity Table in `README.md`, `CLAIMS.md`, `paper/main.tex`, `lean/formalization.yaml` | Direct human inspection of `lean/Challenge.lean` |
| `TM-04` | **Biased or buggy SAT encoding in `exp2`** | False UNSAT lower bounds on Multiplicative Complexity | Zero heuristic symmetry-breaking clauses; every SAT witness checked on all $2^n$ inputs; exhaustive brute-force equivalence test on all 2,048 1-AND circuits ($n=3$) | `test_exp2_bruteforce_sat_encoder_equivalence_n3` |
| `TM-05` | **Float64 rounding presented as exact proof** | Epistemic contamination of exact results | Strict separation: Experiments 1, 2, 3, 4B–4D, 5 use 100% exact integer/`Fraction`/$\mathbb{F}_2$; Attack A RK45 explicitly tagged `numerical_approximation` everywhere | `test_exp4_wild_p_eq_np_falsifiers` |
| `TM-06` | **Bibliographic hallucination / fabricated DOIs** | Reputational and scholarly invalidity | Restricted exclusively to 27 verified foundational publications with zero fabricated DOIs or arXiv numbers | Manual audit during Pass 7 (`docs/10-pass-review.md`) |
| `TM-07` | **Stale `.olean` cache or dirty artifact drift** | Non-reproducible build or mismatched PDF/data | Clean-from-scratch `.lake` rebuild verified; clean-room standalone arXiv tarball compile verified; cryptographic `MANIFEST.sha256` | `scripts/run_all.ps1 -Task all` |
| `TM-08` | **Secret leakage / supply-chain drift** | Credential exposure or unpinned dependency breaks | Offline local execution; zero API keys/tokens; pinned `requirements.lock.txt` and `lean/lean-toolchain`; see `SECURITY.md` | Static scan + `git status` review |
