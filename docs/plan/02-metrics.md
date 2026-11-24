<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Quantitative Exit Criteria & Quality Metrics (`docs/plan/02-metrics.md`)

| Metric | Target | Observed Result | Status |
|---|---|---|---|
| Lean 4.35 clean-room build jobs | 100% pass, 0 warnings | 16/16 jobs, exit 0, 0 warnings (~12 s clean rebuild) | PASS |
| Lean forbidden-token count | 0 hits | 0 hits across 13 files (8,078 lines; max 2,557 lines) | PASS |
| Lean axiom footprint | Strictly $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$ | Verified on all 15 exported theorems (`results/lean_axioms.txt`) | PASS |
| Independent Lean kernel passes | $\ge 5$ working kernels | 6 kernel checks across 5 independent implementations (`results/six_kernel_audit.txt`) | PASS |
| Pytest suite pass rate | 100% pass | 10/10 tests pass in 0.82 s (incl. brute-force $n=3$ SAT encoder audit) | PASS |
| Vector figures visual audit | 4 PDFs, 0 overlapping labels | 4 Type-42 vector PDFs visually verified via `read_file` | PASS |
| AMS-LaTeX compile cleanliness | Exit 0, 0 Overfull/Underfull hbox, 0 undef refs | Exit 0, 0 Overfull/Underfull hboxes, 15 pages visually verified | PASS |
| arXiv tarball standalone build | Exit 0 in clean temp dir | Exit 0 (`174,100` bytes tarball -> `367,071` bytes PDF) | PASS |
| Six-class finding coverage | Every defect classified strictly in 6 labels | 10 findings classified across all 6 labels (`docs/10-pass-review.md`) | PASS |
| Cryptographic manifest | All frozen artifacts hashed | `MANIFEST.sha256` verified 100% | PASS |
