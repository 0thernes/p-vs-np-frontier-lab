<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Configuration & Toolchains (`docs/configuration.md`)

This repository requires **zero runtime API keys, secrets, or network access** after installing pinned toolchains.

| Setting / File | Default / Value | Purpose |
|---|---|---|
| `lean/lean-toolchain` | `leanprover/lean4:v4.35.0` | Pinned Lean 4 compiler & bundled kernels (`leanchecker`, `lean4lean`, `con-leche`, `con-ron`, `nanoda`) |
| `CADICAL_BIN` (env var, optional) | `<lean-toolchain>/bin/cadical[.exe]` | Override path to CaDiCaL 2.1.2 SAT solver used by `exp1` & `exp2` |
| `requirements.lock.txt` | Pinned Python packages | Exact versions of NumPy, SciPy, Matplotlib, pytest, Hypothesis, PyYAML, jsonschema |
| `VERSION` | `1.1.0` | Single version source verified against `CHANGELOG.md` and `CITATION.cff` |
| `ARCHIVE_SYNC_TOKEN` (GitHub Actions secret, optional) | Unset (skips cleanly) | Optional PAT enabling real-time `repository_dispatch` into `0thernes/0thernes-research-archive` |
