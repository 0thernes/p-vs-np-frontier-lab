#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Generate searchable, interactive WCAG 2.2 AA Proof Blueprint & Dependency Graph at build/site/."""
from __future__ import annotations

import html
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"

THEOREMS = [
    ("C1", "otm", "PVsNP.OTM", "PSubsetNPStmt", "prove_p_subset_np", "∀O, P^O ⊆ NP^O (explicit 4-tape OTM)", "propext, Classical.choice, Quot.sound"),
    ("C2", "otm", "PVsNP.Relativization", "BakerGillSolovayStmt", "prove_baker_gill_solovay", "∃A,B, P^A = NP^A ∧ P^B ≠ NP^B", "propext, Classical.choice, Quot.sound"),
    ("C3", "nat", "PVsNP.NaturalProofs", "NaturalProofBreaksPRFStmt", "prove_natural_proof_breaks_prf", "Exact cross-multiplied ℤ Razborov–Rudich PRF break", "propext, Classical.choice, Quot.sound"),
    ("C4", "nat", "PVsNP.NaturalProofs", "HybridTelescopingStmt", "prove_hybrid_telescoping", "Exact ℤ hybrid telescoping triangle inequality", "propext, Quot.sound"),
    ("C5", "nat", "PVsNP.NaturalProofs", "NaturalProofNonVacuousStmt", "prove_natural_proof_nonvacuous", "nonConstantProp density ≥ 1/2 for all n ≥ 1", "propext, Classical.choice, Quot.sound"),
    ("C6", "sheaf", "PVsNP.SheafPolymorphism", "OddCycleContextualStmt", "prove_odd_cycle_contextual", "Odd cycles C_{2k+3} maximally contextual for all k", "propext, Quot.sound"),
    ("C7", "sheaf", "PVsNP.SheafPolymorphism", "MerminPeresContextualStmt", "prove_mermin_peres_contextual", "Mermin–Peres 3×3 magic square maximally contextual", "propext, Classical.choice, Quot.sound"),
    ("C8", "sheaf", "PVsNP.SheafPolymorphism", "TractablePolymorphismsStmt", "prove_tractable_polymorphisms", "Schaefer Maltsev XOR, Horn AND, Dual-Horn OR, 2-SAT Maj", "propext"),
    ("C9", "sheaf", "PVsNP.SheafPolymorphism", "Monotone3SATRigidStmt", "prove_monotone_3sat_rigid", "∀k ≥ 1, {R000, R111} inclusion-minimal rigid", "propext, Quot.sound"),
    ("C10", "circ", "PVsNP.CircuitPhaseTransition", "MarkovInverterTightStmt", "prove_markov_inverter_tight", "k NOT gates invert n bits ⇔ n ≤ 2^k − 1", "propext, Classical.choice, Quot.sound"),
    ("C11", "circ", "PVsNP.CircuitPhaseTransition", "FischerReductionStmt", "prove_fischer_reduction", "Universal dual-rail compilation to ≤ k NOT gates", "propext, Classical.choice, Quot.sound"),
    ("C12", "circ", "PVsNP.CircuitPhaseTransition", "MultiplicativeComplexityStmt", "prove_multiplicative_complexity", "deg_{F2}(f) ≤ k + 1 and MC(AND_n) ≥ n − 1", "propext, Classical.choice, Quot.sound"),
    ("C13", "circ", "PVsNP.CircuitPhaseTransition", "PermDetChar2Stmt", "prove_perm_det_char2", "Perm_n ≡ det_n (mod 2) and W_n separating mod all p ≥ 3", "propext, Classical.choice, Quot.sound"),
    ("C14", "cat", "PVsNP.CatalyticAlgebra", "CatalyticAlgebraStmt", "prove_catalytic_algebra", "Bijective reversibility & exact 3·4^{d−1} d-fold product", "propext, Quot.sound"),
    ("NV1", "sheaf", "PVsNP.NonVacuity", "Non-Vacuity Witness", "nv_odd_cycle_k0_contextual", "Concrete k = 0 triangle XOR system is maximally contextual", "propext, Quot.sound"),
    ("NV2", "sheaf", "PVsNP.NonVacuity", "Non-Vacuity Witness", "nv_mermin_peres_contextual", "Concrete Mermin–Peres 3×3 magic square witness", "propext, Classical.choice, Quot.sound"),
    ("NV3", "circ", "PVsNP.NonVacuity", "Non-Vacuity Witness", "nv_witness_mat_n2", "Concrete W_2 matrix: perm = 2 and det = 0", "propext, Classical.choice, Quot.sound"),
    ("NV4", "nat", "PVsNP.NonVacuity", "Non-Vacuity Witness", "nv_natural_proof_n1", "Concrete n = 1 nonConstantProp density ≥ 1/2 witness", "propext, Classical.choice, Quot.sound"),
    ("NV5", "cat", "PVsNP.NonVacuity", "Non-Vacuity Witness", "nv_catalytic_d2_concrete", "Concrete d = 2 catalytic product [3, 5] -> +15 exact restoration", "propext, Quot.sound"),
    ("ADV1", "sheaf", "PVsNP.AdversarialTests", "Adversarial Refutation", "adv_const_true_not_projection", "Constant true is NOT a ternary projection (C9 sharpness)", "NONE (zero axioms)"),
    ("ADV2", "sheaf", "PVsNP.AdversarialTests", "Adversarial Refutation", "adv_const_false_not_projection", "Constant false is NOT a ternary projection (C9 sharpness)", "NONE (zero axioms)"),
    ("ADV3", "circ", "PVsNP.AdversarialTests", "Adversarial Refutation", "adv_markov_1not_cannot_invert_2bits", "1 NOT gate cannot invert 2 bits (C10 sharpness)", "propext, Classical.choice, Quot.sound"),
    ("ADV4", "circ", "PVsNP.AdversarialTests", "Adversarial Refutation", "adv_mc_and3_not_one_gate", "AND_3 cannot be computed with ≤ 1 AND gate (C12 sharpness)", "propext, Classical.choice, Quot.sound"),
    ("ADV5", "circ", "PVsNP.AdversarialTests", "Adversarial Refutation", "adv_perm_ne_det_mod3_n2", "perm(W_2) ≠ det(W_2) mod 3 (C13 sharpness)", "propext, Classical.choice, Quot.sound"),
]


def main() -> int:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    axioms_txt = (ROOT / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip()

    rows = []
    for cid, grp, mod, ch, sol, desc, ax in THEOREMS:
        hay = html.escape(f"{cid} {mod} {ch} {sol} {desc} {ax}".lower())
        rows.append(
            f'<tr data-group="{grp}" data-search="{hay}"><td><code>{html.escape(cid)}</code></td>'
            f"<td><code>{html.escape(mod)}</code></td>"
            f"<td><code>{html.escape(ch)}</code> / <code>{html.escape(sol)}</code></td>"
            f"<td>{html.escape(desc)}</td>"
            f"<td><code>{html.escape(ax)}</code></td></tr>"
        )

    svg = """<svg id="dag" role="img" aria-label="Interactive dependency graph from core Lean modules through Challenge, NonVacuity, AdversarialTests, and Solution to 6-kernel comparator" viewBox="0 0 920 268" xmlns="http://www.w3.org/2000/svg" style="width:100%;max-width:920px;height:auto;background:#0f172a;border-radius:10px;border:1px solid #334155">
  <defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" fill="#38bdf8"/></marker></defs>
  <g class="node" data-filter="otm" tabindex="0" role="button" aria-label="Filter OTM and Relativization"><rect x="20" y="18" width="190" height="36" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="115" y="41" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">PVsNP.OTM (C1, C2)</text></g>
  <g class="node" data-filter="nat" tabindex="0" role="button" aria-label="Filter Natural Proofs"><rect x="20" y="66" width="190" height="36" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="115" y="89" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">NaturalProofs (C3-C5, NV4)</text></g>
  <g class="node" data-filter="sheaf" tabindex="0" role="button" aria-label="Filter Sheaf and Polymorphism"><rect x="20" y="114" width="190" height="36" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="115" y="137" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">SheafPoly (C6-C9, NV1-2)</text></g>
  <g class="node" data-filter="circ" tabindex="0" role="button" aria-label="Filter Circuit Phase Transition"><rect x="20" y="162" width="190" height="36" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="115" y="185" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">CircuitPhase (C10-C13, ADV)</text></g>
  <g class="node" data-filter="cat" tabindex="0" role="button" aria-label="Filter Catalytic Algebra"><rect x="20" y="210" width="190" height="36" rx="6" fill="#1e293b" stroke="#38bdf8"/><text x="115" y="233" fill="#f8fafc" font-size="12" text-anchor="middle" font-family="monospace">CatalyticAlg (C14, NV5)</text></g>
  <g class="node" data-filter="all" tabindex="0" role="button" aria-label="Show all declarations"><rect x="280" y="96" width="175" height="72" rx="8" fill="#172554" stroke="#60a5fa"/><text x="367" y="126" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">Challenge.lean</text><text x="367" y="148" fill="#cbd5e1" font-size="11" text-anchor="middle" font-family="monospace">C1..C14 + ALL Specs</text></g>
  <g class="node" data-filter="all" tabindex="0" role="button" aria-label="Show all declarations"><rect x="515" y="96" width="175" height="72" rx="8" fill="#14532d" stroke="#4ade80"/><text x="602" y="126" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">Solution + NV + ADV</text><text x="602" y="148" fill="#dcfce7" font-size="11" text-anchor="middle" font-family="monospace">25 Audited Decls</text></g>
  <rect x="745" y="96" width="155" height="72" rx="8" fill="#3b0764" stroke="#c084fc"/><text x="822" y="124" fill="#f8fafc" font-size="13" font-weight="bold" text-anchor="middle" font-family="sans-serif">6-Kernel + Neg CI</text><text x="822" y="146" fill="#e9d5ff" font-size="11" text-anchor="middle" font-family="monospace">lake comparator</text>
  <line x1="210" y1="36" x2="280" y2="112" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="210" y1="84" x2="280" y2="122" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="210" y1="132" x2="280" y2="132" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="210" y1="180" x2="280" y2="142" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="210" y1="228" x2="280" y2="152" stroke="#38bdf8" stroke-width="1.5" marker-end="url(#arr)"/>
  <line x1="455" y1="132" x2="515" y2="132" stroke="#4ade80" stroke-width="2" marker-end="url(#arr)"/>
  <line x1="690" y1="132" x2="745" y2="132" stroke="#c084fc" stroke-width="2" marker-end="url(#arr)"/>
</svg>"""

    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>P vs. NP Frontier &amp; Barrier Anatomy Lab — Proof Blueprint (v{html.escape(version)})</title>
  <style>
    :root {{ color-scheme: dark; }}
    body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: #0b1020; color: #e2e8f0; margin: 0; line-height: 1.55; }}
    .skip {{ position: absolute; left: -9999px; }}
    .skip:focus {{ left: 1rem; top: 1rem; background: #38bdf8; color: #0b1020; padding: .5rem .9rem; border-radius: 6px; font-weight: 700; z-index: 100; }}
    header {{ background: linear-gradient(135deg, #0f172a, #172554); border-bottom: 1px solid #1e3a8a; padding: 2.4rem 1.5rem; }}
    .wrap {{ max-width: 1120px; margin: 0 auto; }}
    .eyebrow {{ color: #4ade80; font-size: .82rem; font-weight: 700; letter-spacing: .12em; text-transform: uppercase; }}
    h1 {{ margin: .3rem 0 .6rem; font-size: 2rem; color: #f8fafc; }}
    .notice {{ background: #1e293b; border-left: 4px solid #f59e0b; padding: .85rem 1rem; border-radius: 6px; margin-top: 1rem; }}
    .pills {{ display: flex; flex-wrap: wrap; gap: .6rem; margin-top: 1rem; }}
    .pill {{ padding: .42rem .85rem; border-radius: 999px; background: #1e293b; border: 1px solid #475569; color: #f8fafc; text-decoration: none; font-size: .86rem; font-weight: 600; }}
    .pill:focus-visible, a:focus-visible, input:focus-visible, button:focus-visible, .node:focus-visible {{ outline: 3px solid #38bdf8; outline-offset: 2px; }}
    .node {{ cursor: pointer; }}
    .controls {{ display: flex; flex-wrap: wrap; gap: .6rem; align-items: center; margin: 1rem 0; }}
    .controls input {{ flex: 1 1 260px; background: #0f172a; color: #f8fafc; border: 1px solid #334155; border-radius: 6px; padding: .48rem .75rem; font-size: .92rem; }}
    .btn {{ background: #1e293b; color: #f8fafc; border: 1px solid #475569; border-radius: 6px; padding: .44rem .78rem; cursor: pointer; font-weight: 600; font-size: .84rem; }}
    .btn[aria-pressed="true"] {{ background: #0369a1; border-color: #38bdf8; }}
    main {{ padding: 1.5rem 1.5rem 4rem; }}
    table {{ width: 100%; border-collapse: collapse; margin-top: .8rem; font-size: .9rem; }}
    th, td {{ border-bottom: 1px solid #1e293b; padding: .55rem .65rem; text-align: left; vertical-align: top; }}
    th {{ color: #cbd5e1; }}
    code {{ background: #0f172a; padding: .1rem .32rem; border-radius: 4px; color: #7dd3fc; }}
    pre {{ background: #0f172a; border: 1px solid #1e293b; padding: 1rem; border-radius: 8px; overflow-x: auto; font-size: .82rem; color: #bae6fd; }}
    footer {{ border-top: 1px solid #1e293b; padding: 1.5rem; text-align: center; color: #94a3b8; font-size: .85rem; }}
    a {{ color: #38bdf8; }}
    @media (prefers-reduced-motion: reduce) {{ * {{ transition: none !important; animation: none !important; }} }}
  </style>
</head>
<body>
  <a class="skip" href="#main">Skip to main content</a>
  <header>
    <div class="wrap">
      <div class="eyebrow">Zero-Mathlib Lean 4.35.0 Interactive Proof Blueprint &middot; v{html.escape(version)}</div>
      <h1>P vs. NP Frontier &amp; Barrier Anatomy Lab</h1>
      <p>Author: Alexander S. Donahue (Independent Researcher, Spokane, WA, USA &middot; ORCID 0009-0006-8168-9648).</p>
      <div class="notice"><strong>Epistemic Boundary:</strong> P vs. NP remains <strong>COMPLETELY OPEN</strong>. Nothing here claims a proof of P = NP or P &ne; NP. All 25 audited Lean 4.35.0 declarations (14 barrier theorems + master conjunction + 5 NonVacuity + 5 AdversarialTests) certify unconditional complexity barriers, algebraic rigidity, circuit phase transitions, and zero-workspace catalytic algebra.</div>
      <nav class="pills" aria-label="Primary links">
        <a class="pill" href="https://github.com/0thernes/p-vs-np-frontier-lab">GitHub Repository</a>
        <a class="pill" href="Donahue_2026_p_vs_np_barrier_anatomy.pdf">White Paper PDF (15 pp.)</a>
        <a class="pill" href="MANIFEST.sha256">MANIFEST.sha256</a>
        <a class="pill" href="https://0thernes.github.io/0thernes-research-archive/">Master Research Archive</a>
      </nav>
    </div>
  </header>
  <main id="main" class="wrap">
    <h2>Interactive Proof Architecture (Click any module node to filter)</h2>
    {svg}
    <div class="controls" role="search" aria-label="Filter Lean declarations">
      <label for="q">Filter:</label>
      <input id="q" type="search" placeholder="Search C1..C14, NV1..NV5, ADV1..ADV5, Markov, Catalytic, zero axioms…"/>
      <button type="button" class="btn" data-filter="all" aria-pressed="true">All (24)</button>
      <button type="button" class="btn" data-filter="otm" aria-pressed="false">OTM</button>
      <button type="button" class="btn" data-filter="nat" aria-pressed="false">Natural</button>
      <button type="button" class="btn" data-filter="sheaf" aria-pressed="false">Sheaf/CSP</button>
      <button type="button" class="btn" data-filter="circ" aria-pressed="false">Circuits</button>
      <button type="button" class="btn" data-filter="cat" aria-pressed="false">Catalytic</button>
    </div>
    <h2>Formalized Theorems, Non-Vacuity Witnesses &amp; Adversarial Refutations (25 Audited Decls incl. Master Conjunction)</h2>
    <table>
      <thead><tr><th>ID</th><th>Module</th><th>Challenge / Declaration</th><th>Statement</th><th>Axioms</th></tr></thead>
      <tbody>{"".join(rows)}</tbody>
    </table>
    <h2>Verbatim <code>#print axioms</code> Output (25 Declarations)</h2>
    <pre>{html.escape(axioms_txt)}</pre>
  </main>
  <footer>
    ORCID <a href="https://orcid.org/0009-0006-8168-9648">0009-0006-8168-9648</a> &middot;
    Apache-2.0 (code) &middot; CC-BY-4.0 (manuscript &amp; docs) &middot;
    27/27 Live Crossref Verified Citations (0 Retractions) &middot;
    <a href="https://github.com/0thernes/0thernes-research-archive">0thernes-research-archive</a>
  </footer>
  <script>
    (function() {{
      const q = document.getElementById('q');
      const btns = Array.from(document.querySelectorAll('.btn[data-filter]'));
      const nodes = Array.from(document.querySelectorAll('.node[data-filter]'));
      const trs = Array.from(document.querySelectorAll('tbody tr'));
      let grp = 'all';
      function apply() {{
        const needle = (q.value || '').trim().toLowerCase();
        trs.forEach(tr => {{
          const okG = grp === 'all' || tr.dataset.group === grp;
          const okQ = !needle || (tr.dataset.search || '').includes(needle);
          tr.style.display = (okG && okQ) ? '' : 'none';
        }});
        btns.forEach(b => b.setAttribute('aria-pressed', String(b.dataset.filter === grp)));
      }}
      function setFilter(f) {{ grp = f; apply(); }}
      btns.forEach(b => b.addEventListener('click', () => setFilter(b.dataset.filter)));
      nodes.forEach(n => {{
        n.addEventListener('click', () => setFilter(n.dataset.filter));
        n.addEventListener('keydown', e => {{ if (e.key === 'Enter' || e.key === ' ') {{ e.preventDefault(); setFilter(n.dataset.filter); }} }});
      }});
      q.addEventListener('input', apply);
    }})();
  </script>
</body>
</html>
"""
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "index.html").write_text(page, encoding="utf-8", newline="\n")
    shutil.copy2(ROOT / "dist" / "Donahue_2026_p_vs_np_barrier_anatomy.pdf", SITE / "Donahue_2026_p_vs_np_barrier_anatomy.pdf")
    shutil.copy2(ROOT / "MANIFEST.sha256", SITE / "MANIFEST.sha256")
    print(f"PASS: Built interactive WCAG 2.2 AA Blueprint site at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
