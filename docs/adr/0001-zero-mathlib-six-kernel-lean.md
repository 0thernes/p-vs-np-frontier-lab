# ADR 0001: Zero-Mathlib Lean 4.35.0 Architecture & Six-Kernel Replay

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

- **Date:** 2026-11-23
- **Status:** Accepted
- **Context:** Lean 4.35.0 ships with six independent kernel/checker executables (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) plus `lake check` and `lake comparator`. Adding Mathlib4 pulls >100k declarations, drastically expands the export size and trusted-code base, and slows independent multi-kernel replay from seconds to hours.
- **Decision:** Build the entire `PVsNP` formalization on **zero external Lake dependencies** (pure Lean 4.35.0 `Init` / `Std` core), structured with a short, human-auditable `Challenge.lean` and a separate `Solution.lean` plus `VerifyAxioms.lean` and `formalization.yaml` (Palomar Registry convention: `module` headers, ≤ 10,000 lines per file, `autoImplicit = false`).
- **Consequences:**
  - Clean rebuild from empty `.lake/` completes in ~12 seconds (16/16 jobs, 0 warnings).
  - Six independent kernel checks across five distinct implementations (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) pass with exit code `0` (`results/six_kernel_audit.txt`). Upstream Windows packaging `issue`: the bundled `lean4lean.exe` rejects even stdlib `Init.Prelude.olean` (`incompatible header`), and `lake check` requires Linux `bwrap`/`git`; both are documented honestly in `LIMITATIONS.md` and `docs/10-pass-review.md`.
  - Trade-off (`dilemma`): Batteries `#lint` / `lake exe runLinter` are not bundled in the core package; we mitigate with strict `autoImplicit = false`, `relaxedAutoImplicit = false`, zero compiler warnings, and automated forbidden-token / axiom / signature tests in `tests/test_all.py`.
