#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify verbatim #print axioms parity between README.md and results/lean_axioms.txt."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL_PREFIXES = ("'Solution.", "'PVsNP.NonVacuity.", "'PVsNP.AdversarialTests.")


def main() -> int:
    ax_path = ROOT / "results" / "lean_axioms.txt"
    readme_path = ROOT / "README.md"
    if not ax_path.exists():
        print(f"ERROR: missing {ax_path}", file=sys.stderr)
        return 1

    ax_lines = [
        ln.strip()
        for ln in ax_path.read_text(encoding="utf-8").splitlines()
        if ln.strip().startswith(DECL_PREFIXES)
    ]
    if len(ax_lines) != 25:
        print(f"ERROR: expected 25 audited declarations in results/lean_axioms.txt, got {len(ax_lines)}", file=sys.stderr)
        return 1

    readme_txt = readme_path.read_text(encoding="utf-8")
    errors: list[str] = []
    for ln in ax_lines:
        m_dep = re.match(r"^'([\w\.]+)' depends on axioms: \[([^\]]*)\]$", ln)
        m_zero = re.match(r"^'([\w\.]+)' does not depend on any axioms$", ln)
        if m_dep:
            name, raw_ax = m_dep.groups()
            used = {a.strip() for a in raw_ax.split(",") if a.strip()}
            if not used.issubset(ALLOWED):
                errors.append(f"{name} uses disallowed axioms: {sorted(used - ALLOWED)}")
        elif not m_zero:
            errors.append(f"Unrecognized axiom line: {ln}")
            continue
        if ln not in readme_txt:
            errors.append(f"README.md missing verbatim axiom line: {ln}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1

    print(f"PASS: All {len(ax_lines)} verbatim #print axioms lines match README.md and stay within {sorted(ALLOWED)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
