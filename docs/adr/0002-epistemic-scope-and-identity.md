# ADR 0002: Epistemic Scope, Legal Identity, and License Compliance

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

- **Date:** 2026-11-23
- **Status:** Accepted
- **Context (Classified `conflict`):** Older workspace identity notes listed `0thernes LLC` as author affiliation and copyright holder and MIT as default code license. However, the live audit in `I:\White Papers\DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md` (Nov 22–24, 2026, Findings #1, #3, #4) documented that no LLC entity has yet been legally formed, that asserting copyright/affiliation for a non-existent LLC undermines external credibility, and that Apache-2.0 aligns with Mathlib/Lean community standards while CC-BY-4.0 fits open academic prose.
- **Decision:**
  1. List author as `Alexander S. Donahue` (independent researcher, ORCID `0009-0006-8168-9648`, Spokane, WA, USA) — omitting any unformed LLC claim.
  2. Dual-license as **Apache-2.0** (code: `lean/`, `scripts/`, `experiments/`, `tests/`, `.github/`) and **CC-BY-4.0** (manuscripts, documentation, figures: `paper/`, `docs/`, `dist/`, `README.md`).
  3. State upfront on page 1 of the README and white paper that `P vs NP` remains **OPEN**, that no resolution of `P = NP` or `P ≠ NP` is claimed, and disclose AI-assisted proof/drafting transparently with CRediT human-accountability roles.
- **Consequences:** Resolves Playbook Findings #1–#4 cleanly before first release and ensures eligibility for open formalization registries (Palomar) and community scrutiny.
