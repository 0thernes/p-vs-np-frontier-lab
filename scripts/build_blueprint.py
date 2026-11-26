#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Generate static WCAG 2.2 AA interactive Proof Blueprint & Dependency Graph at build/site/."""
from __future__ import annotations

import html
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"

THEOREMS = [
    ("C1", "PVsNP.OTM", "PSubsetNPStmt", "prove_p_subset_np", "∀O, P^O ⊆ NP^O (explicit 4-tape OTM)", "propext, Classical.choice, Quot.sound"),
    ("C2", "PVsNP.Relativization", "BakerGillSolovayStmt", "prove_baker_gill_solovay", "∃A,B, P^A = NP^A ∧ P^B ≠ NP^B", "propext, Classical.choice, Quot.sound"),
    ("C3", "PVsNP.NaturalProofs", "NaturalProofBreaksPRFStmt", "prove_natural_proof_breaks_prf", "Exact cross-multiplied ℤ Razborov–Rudich PRF break", "propext, Classical.choice, Quot.sound"),
    ("C4", "PVsNP.NaturalProofs", "HybridTelescopingStmt", "prove_hybrid_telescoping", "Exact ℤ hybrid telescoping triangle inequality", "propext, Quot.sound"),
    ("C5", "PVsNP.NaturalProofs", "NaturalProofNonVacuousStmt", "prove_natural_proof_nonvacuous", "nonConstantProp density ≥ 1/2 for all n ≥ 1", "propext, Classical.choice, Quot.sound"),
    ("C6", "PVsNP.SheafPolymorphism", "OddCycleContextualStmt", "prove_odd_cycle_contextual", "Odd cycles C_{2k+3} maximally contextual for all k", "propext, Quot.sound"),
    ("C7", "PVsNP.SheafPolymorphism", "MerminPeresContextualStmt", "prove_mermin_peres_contextual", "Mermin–Peres 3×3 magic square maximally contextual", "propext, Classical.choice, Quot.sound"),
    ("C8", "PVsNP.SheafPolymorphism", "TractablePolymorphismsStmt", "prove_tractable_polymorphisms", "Schaefer Maltsev XOR, Horn AND, Dual-Horn OR, 2-SAT Maj", "propext"),
    ("C9", "PVsNP.SheafPolymorphism", "Monotone3SATRigidStmt", "prove_monotone_3sat_rigid", "∀k ≥ 1, {R000, R111} inclusion-minimal rigid", "propext, Quot.sound"),
    ("C10", "PVsNP.CircuitPhaseTransition", "MarkovInverterTightStmt", "prove_markov_inverter_tight", "k NOT gates invert n bits ⇔ n ≤ 2^k − 1", "propext, Classical.choice, Quot.sound"),
    ("C11", "PVsNP.CircuitPhaseTransition", "FischerReductionStmt", "prove_fischer_reduction", "Universal dual-rail compilation to ≤ k NOT gates", "propext, Classical.choice, Quot.sound"),
    ("C12", "PVsNP.CircuitPhaseTransition", "MultiplicativeComplexityStmt", "prove_multiplicative_complexity", "deg_{F2}(f) ≤ k + 1 and MC(AND_n) ≥ n − 1", "propext, Classical.choice, Quot.sound"),
    ("C13", "PVsNP.CircuitPhaseTransition", "PermDetChar2Stmt", "prove_perm_det_char2", "Perm_n ≡ det_n (mod 2) and W_n separating mod all p ≥ 3", "propext, Classical.choice, Quot.sound"),
    ("C14", "PVsNP.CatalyticAlgebra", "CatalyticAlgebraStmt", "prove_catalytic_algebra", "Bijective reversibility & exact 3·4^{d−1} d-fold product", "propext, Quot.sound"),
]


def main() -> int:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    axioms_txt = (ROOT / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip()

    rows = []
    for cid, mod, ch, sol, desc, ax in THEOREMS:
        rows.append(
            f"<tr><td><code>{html.escape(cid)}</code></td>"
            f"<td><code>{html.escape(mod)}</code></td>"
            f"<td><code>{html.escape(ch)}</code> / <code>{html.escape(sol)}</code></td>"
            f"<td>{html.escape(desc)}</td>"
            f"<td><code>{html.escape(ax)}</code></td></tr>"
        )

    svg = """<svg role="img" aria-label="Dependency graph from 6 core Lean modules through Challenge and Solution to Palomar 6-kernel comparator" viewBox="0 0 920 260" xmlns="http://www.w3.org/2000/svg" style="width:100%;max-width:920px;height:auto;background:#0f172a;border-radius:10px;border:1px solid #334155">
  <defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" fill="#38bdf8"/></marker></defs>
  <rect x="20" y="20" width="180" height="34" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="110" y="42" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">PVsNP.OTM (C1,C2)</text>
  <rect x="20" y="66" width="180" height="34" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="110" y="88" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">NaturalProofs (C3-C5)</text>
  <rect x="20" y="112" width="180" height="34" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="110" y="134" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">SheafPoly (C6-C9)</text>
  <rect x="20" y="158" width="180" height="34" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="110" y="180" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">CircuitPhase (C10-C13)</text>
  <rect x="20" y="204" width="180" height="34" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="110" y="226" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">CatalyticAlg (C14)</text>
  <rect x="275" y="96" width="175" height="68" rx="8" fill="#172554" stroke="#60a5fa"/><text x="362" y="124" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">Challenge.lean</text><text x="362" y="146" fill="#cbd5e1" font-size="11" text-anchor="middle" font-family="monospace">C1..C14 + ALL Specs</text>
  <rect x="510" y="96" width="175" height="68" rx="8" fill="#14532d" stroke="#4ade80"/><text x="597" y="124" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">Solution.lean</text><text x="597" y="146" fill="#dcfce7" font-size="11" text-anchor="middle" font-family="monospace">15 Proved Targets</text>
  <rect x="740" y="96" width="160" height="68" rx="8" fill="#3b0764" stroke="#c084fc"/><text x="820" y="122" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">6-Kernel Audit</text><text x="820" y="144" fill="#e9d5ff" font-size="11" text-anchor="middle" font-family="monospace">lake comparator</text>
  <line x1="200" y1="37" x2="275" y2="112" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="200" y1="83" x2="275" y2="120" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="200" y1="129" x2="275" y2="130" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="200" y1="175" x2="275" y2="140" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="200" y1="221" x2="275" y2="148" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="450" y1="130" x2="510" y2="130" stroke="#4ade80" stroke-width="2" marker-end="url(#arr)"/>
  <line x1="685" y1="130" x2="740" y2="130" stroke="#c084fc" stroke-width="2" marker-end="url(#arr)"/>
</svg>"""

    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>P vs. NP Frontier &amp; Barrier Anatomy Lab — Proof Blueprint ({html.escape(version)})</title>
  <style>
    :root {{ color-scheme: dark; }}
    body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: #0b1020; color: #e2e8f0; margin: 0; line-height: 1.55; }}
    .skip {{ position: absolute; left: -9999px; }}
    .skip:focus {{ left: 1rem; top: 1rem; background: #38bdf8; color: #0b1020; padding: .5rem .9rem; border-radius: 6px; font-weight: 700; z-index: 100; }}
    header {{ background: linear-gradient(135deg, #0f172a, #172554); border-bottom: 1px solid #1e3a8a; padding: 2.4rem 1.5rem; }}
    .wrap {{ max-width: 1100px; margin: 0 auto; }}
    .eyebrow {{ color: #4ade80; font-size: .82rem; font-weight: 700; letter-spacing: .12em; text-transform: uppercase; }}
    h1 {{ margin: .3rem 0 .6rem; font-size: 2rem; color: #f8fafc; }}
    .notice {{ background: #1e293b; border-left: 4px solid #f59e0b; padding: .85rem 1rem; border-radius: 6px; margin-top: 1rem; }}
    .pills {{ display: flex; flex-wrap: wrap; gap: .6rem; margin-top: 1rem; }}
    .pill {{ padding: .42rem .85rem; border-radius: 999px; background: #1e293b; border: 1px solid #475569; color: #f8fafc; text-decoration: none; font-size: .86rem; font-weight: 600; }}
    .pill:focus-visible, a:focus-visible {{ outline: 3px solid #38bdf8; outline-offset: 2px; }}
    main {{ padding: 1.5rem 1.5rem 4rem; }}
    table {{ width: 100%; border-collapse: collapse; margin-top: .8rem; font-size: .9rem; }}
    th, td {{ border-bottom: 1px solid #1e293b; padding: .55rem .65rem; text-align: left; vertical-align: top; }}
    th {{ color: #cbd5e1; }}
    code {{ background: #0f172a; padding: .1rem .32rem; border-radius: 4px; color: #7dd3fc; }}
    pre {{ background: #0f172a; border: 1px solid #1e293b; padding: 1rem; border-radius: 8px; overflow-x: auto; font-size: .82rem; color: #bae6fd; }}
    footer {{ border-top: 1px solid #1e293b; padding: 1.5rem; text-align: center; color: #94a3b8; font-size: .85rem; }}
    a {{ color: #38bdf8; }}
  </style>
</head>
<body>
  <a class="skip" href="#main">Skip to main content</a>
  <header>
    <div class="wrap">
      <div class="eyebrow">Zero-Mathlib Lean 4.35.0 Proof Blueprint &middot; v{html.escape(version)}</div>
      <h1>P vs. NP Frontier &amp; Barrier Anatomy Lab</h1>
      <p>Author: Alexander S. Donahue (Independent Researcher, Spokane, WA, USA &middot; ORCID 0009-0006-8168-9648).</p>
      <div class="notice"><strong>Epistemic Boundary:</strong> P vs. NP remains <strong>COMPLETELY OPEN</strong>. Nothing here claims a proof of P = NP or P &ne; NP. All 14 theorems certify unconditional complexity barriers, algebraic rigidity, circuit phase transitions, and zero-workspace catalytic algebra.</div>
      <nav class="pills" aria-label="Primary links">
        <a class="pill" href="https://github.com/0thernes/p-vs-np-frontier-lab">GitHub Repository</a>
        <a class="pill" href="Donahue_2026_p_vs_np_barrier_anatomy.pdf">White Paper PDF (15 pp.)</a>
        <a class="pill" href="MANIFEST.sha256">MANIFEST.sha256</a>
        <a class="pill" href="https://0thernes.github.io/0thernes-research-archive/">Master Research Archive</a>
      </nav>
    </div>
  </header>
  <main id="main" class="wrap">
    <h2>Interactive Proof Architecture</h2>
    {svg}
    <h2>14 Formalized Barrier &amp; Rigidity Theorems (C1&ndash;C14)</h2>
    <table>
      <thead><tr><th>ID</th><th>Module</th><th>Challenge / Solution</th><th>Statement</th><th>Axioms</th></tr></thead>
      <tbody>{"".join(rows)}</tbody>
    </table>
    <h2>Verbatim <code>#print axioms</code> Output</h2>
    <pre>{html.escape(axioms_txt)}</pre>
  </main>
  <footer>
    ORCID <a href="https://orcid.org/0009-0006-8168-9648">0009-0006-8168-9648</a> &middot;
    Apache-2.0 (code) &middot; CC-BY-4.0 (manuscript &amp; docs) &middot;
    <a href="https://github.com/0thernes/0thernes-research-archive">0thernes-research-archive</a>
  </footer>
</body>
</html>
"""
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "index.html").write_text(page, encoding="utf-8", newline="\n")
    shutil.copy2(ROOT / "dist" / "Donahue_2026_p_vs_np_barrier_anatomy.pdf", SITE / "Donahue_2026_p_vs_np_barrier_anatomy.pdf")
    shutil.copy2(ROOT / "MANIFEST.sha256", SITE / "MANIFEST.sha256")
    print(f"PASS: Built Blueprint site at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
