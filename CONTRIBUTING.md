<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Contributing to `p-vs-np-frontier-lab`

## Workflow (Build Standard v1.2.0 Solo-Maintainer Rules)

- All commits land directly on `main` (`R1`/`R2`); CI is informational only (`R3`) and never blocks commits or pushes.
- There are no PR templates, no Dependabot auto-PRs, and no required branch-protection gates (`R4`).
- Use GitHub Issues (`.github/ISSUE_TEMPLATE/`) for bug reports, mathematical critiques, statement-fidelity audits, and independent replication reports, classifying every finding under exactly one of the 10 Build Standard classes (`docs/glossary.md`).

## Setup & Verification Commands

```bash
python3 -m pip install -r requirements.lock.txt
just test
just axioms
just lean
just reproduce
```

## Epistemic Standards

- Never fabricate test outputs, Lean axioms, DOIs, or claims (`R6`).
- Any claim of `P = NP` or `P != NP` is explicitly out of scope unless accompanied by a complete, fidelity-audited, multi-kernel Lean 4 formalization.
