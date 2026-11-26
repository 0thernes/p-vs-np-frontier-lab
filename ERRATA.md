<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata & Corrections Log (`ERRATA.md`)

This append-only ledger records every mathematical, formalization, documentation, or provenance correction after release (Defensible Independent AI Research Playbook v1.3, item #39).

## `v1.1.0` (2026-11-25)
- **Zero mathematical errata in theorems `C1`–`C14` or white paper PDF.**
- **Provenance & packaging upgrade:** Added isolated `lean/PalomarChallenge.lean`, `lean/PalomarSolution.lean`, and `lean/comparator.json` so all 15 exported targets pass `lake comparator --config comparator.json --paranoid` on Ubuntu CI across all 6 independent kernels; upgraded repository metadata from Build Standard v1.1.0 (6 classes) to v1.2.0 (10 classes) prior to initial public GitHub publication.
- **Withdrawal plan:** Should any fatal defect ever be identified in a published theorem statement or empirical experiment, a dated entry will be appended here, the README and CLAIMS ledger will mark the affected claim `retracted`, and a new versioned tag will be cut without rewriting prior git history.
