<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Third-Party Notices

This repository contains zero vendored third-party libraries and zero Mathlib code. It depends on the following external tools at build/verification time:

| Component | License | Role |
|---|---|---|
| Lean 4 (`v4.35.0`) & bundled kernels (`leanchecker`, `lean4lean`, `con-leche`, `con-ron`, `nanoda`) | Apache-2.0 / MIT | Formal proof checking & 6-kernel comparator |
| CaDiCaL 2.1.2 (bundled with Lean 4.35.0) | MIT | Exact SAT/UNSAT verification in `exp1` & `exp2` |
| Python 3 (`requirements.lock.txt`: NumPy, SciPy, Matplotlib, pytest, Hypothesis, PyYAML, jsonschema) | BSD-3-Clause / PSF / MIT / MPL-2.0 | Exact-arithmetic experiments, vector figures, automated tests |
| Tectonic (`amsart`) | MIT | AMS-LaTeX white paper PDF compilation |
