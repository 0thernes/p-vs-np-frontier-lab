<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# AGENTS.md — Canonical Agent & Maintainer Entry Point

- **Project:** `p-vs-np-frontier-lab` — Machine-Checked Barrier Anatomy and Twelve Divergent Pathways Toward P vs. NP (`v1.1.0`)
- **Repository:** `https://github.com/0thernes/p-vs-np-frontier-lab` · **Master Archive:** `0thernes/0thernes-research-archive` (`0TH-2026-013`)
- **Author:** Alexander S. Donahue (`Independent Researcher, Spokane, WA, USA`, ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`). Never assert an unformed LLC entity.
- **Epistemic Status of P vs NP:** **COMPLETELY OPEN.** This repository proves **neither** `P = NP` **nor** `P != NP`. All 14 Lean 4.35.0 theorems (`C1`–`C14`) establish unconditional complexity barriers, polymorphism rigidity, circuit phase transitions, and zero-workspace catalytic algebra.

## Hard Rules (`R1`–`R8`)

1. Commit and push straight to `main` (`R1`/`R2`); CI is informational only (`R3`); zero banned files (`PULL_REQUEST_TEMPLATE.md`, `dependabot.yml`, `copilot-instructions.md`, `FUNDING.yml`) (`R4`).
2. Never fabricate outputs, Lean axioms, DOIs, or peer-review claims (`R6`).
3. Classify every finding under exactly one of the 10 Build Standard v1.2.0 classes (`R7`; `docs/glossary.md`): `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`.
4. Zero `sorry`, `admit`, `native_decide`, custom `axiom`, `implemented_by`, or `@[extern]` in all proof modules (`lean/PVsNP/*`, `Challenge.lean`, `Solution.lean`, `PalomarSolution.lean`). Only `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) contains intentional comparator challenge placeholders matched against sorry-free `PalomarSolution.lean`.
5. PowerShell bracket-safety (Windows ReFS `Z:\[Vibe Coded (AI)]`): always use `-LiteralPath` in PowerShell file cmdlets.

## Core Commands

```bash
just lean        # Clean zero-Mathlib Lean 4.35.0 build + verbatim #print axioms
just test        # Run pytest exact-arithmetic, brute-force SAT, Hypothesis & negative suite
just axioms      # Verify verbatim #print axioms parity between README.md and results/lean_axioms.txt
just site        # Build WCAG 2.2 AA static Proof Blueprint site at build/site/
just reproduce   # Run tests, axiom parity, blueprint build, SHA-256 check, and Build Standard audit
just audit       # Score repository against Build Standard v1.2.0 (docs/build-standard.md)
```
