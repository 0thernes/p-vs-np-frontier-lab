# SPDX-License-Identifier: Apache-2.0
"""
Generate 4 publication-grade vector PDF figures for the AMS-LaTeX white paper
from verified JSON outputs in results/. Uses colorblind-safe Okabe-Ito palette,
crisp serif typography, and zero overlapping labels.
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import ListedColormap
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "legend.fontsize": 8.3,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})

C_BLUE = "#0072B2"
C_VERMILION = "#D55E00"
C_GREEN = "#009E73"
C_ORANGE = "#E69F00"
C_SKY = "#56B4E9"
C_DARK = "#222222"
C_GRAY = "#555555"


def load_json(name: str) -> dict:
    return json.loads((RESULTS / name).read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# Figure 1: Tseitin Maximal Contextuality — CDCL Explosion vs F2 Linear Ops
# ---------------------------------------------------------------------------

def make_fig1() -> None:
    data = load_json("exp1_polymorphism_contextuality.json")
    rows = data["tseitin_3reg_scaling"]
    verts = [r["vertices"] for r in rows]
    f2_ops = [r["f2_gaussian_row_ops"] for r in rows]
    conflicts = [r["cadical"]["conflicts"] for r in rows]
    props = [r["cadical"]["propagations"] for r in rows]

    fig, ax = plt.subplots(figsize=(6.4, 3.7))
    ax.semilogy(
        verts, conflicts, marker="o", linewidth=2.0, markersize=6,
        color=C_VERMILION, label="CaDiCaL 2.1.2 CDCL conflicts (Resolution-based)"
    )
    ax.semilogy(
        verts, props, marker="^", linewidth=1.4, linestyle="--", markersize=5,
        color=C_ORANGE, alpha=0.88, label="CaDiCaL 2.1.2 unit propagations"
    )
    ax.semilogy(
        verts, f2_ops, marker="s", linewidth=2.2, markersize=6,
        color=C_BLUE, label=r"Exact $\mathbb{F}_2$ Gaussian elimination row ops ($V-1$)"
    )

    # Place annotations cleanly in open white pockets away from all 3 curves
    ax.annotate(
        f"{conflicts[-1]:,} conflicts\n(V={verts[-1]}, 69 vars)",
        xy=(verts[-1], conflicts[-1]),
        xytext=(33.5, 550.0),
        fontsize=8.2, color=C_VERMILION, fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=C_VERMILION, alpha=0.92),
        arrowprops=dict(arrowstyle="->", color=C_VERMILION, lw=1.1, connectionstyle="arc3,rad=0.15"),
    )
    ax.annotate(
        f"{f2_ops[-1]} row ops\n(linear in V)",
        xy=(verts[-1], f2_ops[-1]),
        xytext=(34.5, 9.0),
        fontsize=8.2, color=C_BLUE, fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=C_BLUE, alpha=0.92),
        arrowprops=dict(arrowstyle="->", color=C_BLUE, lw=1.1, connectionstyle="arc3,rad=-0.1"),
    )

    ax.set_xlabel("Tseitin 3-regular twisted-chord graph vertices $V$ (all maximally contextual)")
    ax.set_ylabel("Exact operation / conflict count (log scale)")
    ax.set_title("Maximal Sheaf Contextuality Does Not Separate P from NP (Maltsev Bypass)")
    ax.set_xticks(verts)
    ax.set_ylim(5, 1.2e6)
    ax.grid(True, which="both", linestyle=":", alpha=0.35)
    ax.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.95)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_tseitin_contextuality_vs_f2.pdf", bbox_inches="tight", metadata={"CreationDate": None})
    plt.close(fig)


# ---------------------------------------------------------------------------
# Figure 2: Exact Multiplicative Complexity (MC) vs Degree Bound Frontier
# ---------------------------------------------------------------------------

def make_fig2() -> None:
    data = load_json("exp2_multiplicative_complexity.json")
    exact_rows = [r for r in data["results"] if r["status"] == "EXACT"]

    exact_rows.sort(key=lambda r: (r["n"], r["mc"], r["gap_above_deg_minus_1"], r["name"]))
    labels = []
    for r in exact_rows:
        short = (
            r["name"]
            .replace(" (exact weight 2)", "")
            .replace(" (exact weight 3)", "")
            .replace(" (w % 3 == 0)", "")
            .replace(" (w % 3 == 1)", "")
            .replace(" (x0x1 ^ x2x3)", "")
            .replace(" (x0|x1|x2)", "")
            .replace(" (TH_2^3)", "")
            .replace(" (TH_3^5)", "")
        )
        labels.append(f"{short} (n={r['n']})")

    y = np.arange(len(exact_rows))
    deg_lb = [r["deg"] - 1 for r in exact_rows]
    mc_vals = [r["mc"] for r in exact_rows]
    gaps = [r["gap_above_deg_minus_1"] for r in exact_rows]

    fig, ax = plt.subplots(figsize=(6.6, 5.5))
    bar_h = 0.38
    ax.barh(y - bar_h / 2, deg_lb, height=bar_h, color=C_SKY, edgecolor=C_DARK, linewidth=0.5)

    mc_colors = [C_VERMILION if g > 0 else C_BLUE for g in gaps]
    ax.barh(y + bar_h / 2, mc_vals, height=bar_h, color=mc_colors, edgecolor=C_DARK, linewidth=0.5)

    for i, r in enumerate(exact_rows):
        if r["gap_above_deg_minus_1"] > 0:
            ax.text(
                r["mc"] + 0.08, i + bar_h / 2,
                f"MC={r['mc']} (+1 gap, NL={r['nonlinearity']})",
                va="center", fontsize=7.8, color=C_VERMILION, fontweight="bold",
            )
        else:
            ax.text(
                r["mc"] + 0.08, i + bar_h / 2,
                f"MC={r['mc']} (AI={r['ai']}, NL={r['nonlinearity']})",
                va="center", fontsize=7.4, color=C_DARK,
            )

    handles = [
        mpatches.Patch(facecolor=C_SKY, edgecolor=C_DARK, label=r"Degree bound $\deg_{\mathbb{F}_2}(f)-1$"),
        mpatches.Patch(facecolor=C_BLUE, edgecolor=C_DARK, label=r"Exact $\mathrm{MC}(f)$ (tight)"),
        mpatches.Patch(facecolor=C_VERMILION, edgecolor=C_DARK, label=r"Strict gap ($\Delta=+1$)"),
    ]
    ax.set_yticks(y)
    ax.set_yticklabels(labels)
    ax.set_xlabel("Number of AND (non-Clifford) gates")
    ax.set_xlim(0, 6.2)
    ax.set_title(r"Exact Multiplicative Complexity vs. $\mathbb{F}_2$-Degree Bound ($n \in \{3,4,5\}$)", pad=28)
    ax.grid(True, axis="x", linestyle=":", alpha=0.4)
    ax.legend(
        handles=handles, loc="upper center", bbox_to_anchor=(0.48, 1.08),
        ncol=3, frameon=True, facecolor="white", framealpha=0.95, fontsize=7.8,
        columnspacing=1.0, handletextpad=0.4,
    )
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_mc_degree_frontier.pdf", bbox_inches="tight", metadata={"CreationDate": None})
    plt.close(fig)


# ---------------------------------------------------------------------------
# Figure 3: Markov Bounded-Negation Threshold & Catalytic Time-Space Curve
# ---------------------------------------------------------------------------

def make_fig3() -> None:
    data = load_json("exp3_markov_and_catalytic.json")
    mk = data["markov_inverter"]
    cat = data["catalytic_multilinear_scaling"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.8, 3.4))

    # Panel (a): Markov threshold k vs 2^k - 1
    ks = [r["k_not_gates"] for r in mk]
    ns = [r["n_variables_inverted"] for r in mk]
    k_cont = np.linspace(0.7, 4.3, 200)
    ax1.fill_between(k_cont, 0, np.power(2.0, k_cont) - 1.0, color=C_SKY, alpha=0.18,
                     label=r"Feasible ($n \leq 2^k - 1$)")
    ax1.plot(k_cont, np.power(2.0, k_cont) - 1.0, color=C_BLUE, linewidth=1.8,
             label=r"Markov boundary $n = 2^k - 1$")
    ax1.scatter(ks, ns, color=C_VERMILION, s=55, zorder=5,
                label="Exhaustively verified circuits")
    offsets = {1: (-10, 10), 2: (-28, 7), 3: (-32, 7), 4: (-18, -16)}
    for k, n in zip(ks, ns):
        ax1.annotate(f"({k}, {n})", (k, n), textcoords="offset points", xytext=offsets[k],
                     fontsize=7.8, fontweight="bold", color=C_DARK)
    ax1.set_xlabel("NOT gate budget $k$")
    ax1.set_ylabel("Max inverted variables $n$")
    ax1.set_title("(a) Markov Bounded-Negation Threshold")
    ax1.set_xticks(ks)
    ax1.set_ylim(0, 19.0)
    ax1.grid(True, linestyle=":", alpha=0.4)
    ax1.legend(loc="upper left", fontsize=7.3, frameon=True, facecolor="white")

    # Panel (b): Catalytic exact T(d) = 3 * 4^(d-1) - 2 vs clean-workspace O(d)
    ds = [r["degree_d"] for r in cat]
    ops = [r["primitive_ops"] for r in cat]
    clean_ops = [2 * d - 1 for d in ds]

    ax2.semilogy(ds, ops, marker="o", linewidth=2.0, markersize=5.5, color=C_VERMILION,
                 label=r"Zero-workspace catalytic: $3\cdot 4^{d-1}-2$")
    ax2.semilogy(ds, clean_ops, marker="s", linewidth=1.6, linestyle="--", markersize=4.5,
                 color=C_GREEN, label=r"Clean-workspace baseline ($2d-1$)")
    ax2.annotate(
        f"d=8: {ops[-1]:,} ops\n0 clean regs, 0 corruptions",
        xy=(ds[-1], ops[-1]), xytext=(4.1, 45.0),
        fontsize=7.0, color=C_VERMILION, fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=C_VERMILION, alpha=0.94),
        arrowprops=dict(arrowstyle="->", color=C_VERMILION, lw=1.0, connectionstyle="arc3,rad=0.22"),
    )
    ax2.set_xlabel("Multilinear product degree $d$ (catalysts used)")
    ax2.set_ylabel("Exact reversible ops (log scale)")
    ax2.set_title("(b) Catalytic Zero-Workspace Cost")
    ax2.set_xticks(ds)
    ax2.set_ylim(0.7, 8e5)
    ax2.grid(True, which="both", linestyle=":", alpha=0.35)
    ax2.legend(loc="upper left", fontsize=7.3, frameon=True, facecolor="white")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_markov_and_catalytic_tradeoffs.pdf", bbox_inches="tight", metadata={"CreationDate": None})
    plt.close(fig)


# ---------------------------------------------------------------------------
# Figure 4: 12-Path Barrier Gauntlet Matrix & CTDS Planted vs UNSAT Energy
# ---------------------------------------------------------------------------

def make_fig4() -> None:
    exp4 = load_json("exp4_wild_p_eq_np_falsifiers.json")

    fig, (ax1, ax2) = plt.subplots(
        1, 2, figsize=(7.0, 4.4), gridspec_kw={"width_ratios": [1.35, 1.05]}
    )

    paths = [
        "1. Sheaf / Contextuality",
        "2. Quantum Contextuality",
        "3. Polymorphism Rigidity",
        "4. MC / Magic Gates",
        "5. Bounded Negation",
        "6. Tropical / Semiring",
        "7. Landauer / Reversible",
        "8. Spin-Glass OGP",
        "9. Char-2 Perm/Det",
        "10. Catalytic / Sqrt Space",
        "11. Bounded Arithmetic",
        "12. 4 Wild P=NP Attacks",
    ]
    barriers = ["Relat.", "NatPrf", "Algeb.", "Meta-C", "Phys."]
    matrix = np.array([
        [1, 1, 0, 0, 1],
        [1, 1, 0, 0, 1],
        [1, 1, 1, 0, 1],
        [1, 0, 1, 0, 1],
        [1, 0, 1, 0, 1],
        [1, 0, 0, 0, 1],
        [1, 1, 1, 1, 0],
        [1, 0, 0, 0, 1],
        [1, 1, 1, 2, 1],
        [1, 1, 1, 2, 1],
        [1, 1, 1, 2, 1],
        [0, 0, 0, 0, 0],
    ])

    cmap = ListedColormap(["#F4C2C2", "#CFE2F3", "#D9EAD3"])
    ax1.imshow(matrix, cmap=cmap, aspect="auto", vmin=0, vmax=2)

    sym_map = {0: "BLK", 1: "INS", 2: "OPN"}
    txt_col = {0: "#990000", 1: "#0B5394", 2: "#274E13"}
    for r in range(matrix.shape[0]):
        for c in range(matrix.shape[1]):
            val = int(matrix[r, c])
            ax1.text(c, r, sym_map[val], ha="center", va="center",
                     fontsize=7.0, fontweight="bold", color=txt_col[val])

    ax1.set_xticks(range(len(barriers)))
    ax1.set_xticklabels(barriers, fontsize=8.0)
    ax1.set_yticks(range(len(paths)))
    ax1.set_yticklabels(paths, fontsize=7.6)
    ax1.set_title("(a) 12 Wild Paths vs. 5-Barrier Gauntlet", fontsize=9.8)
    for x in np.arange(-0.5, len(barriers), 1):
        ax1.axvline(x, color="white", linewidth=1.0)
    for y in np.arange(-0.5, len(paths), 1):
        ax1.axhline(y, color="white", linewidth=1.0)

    # Panel (b): Attack A CTDS ODE — Planted SAT vs Exact UNSAT
    sat_recs = exp4["attack_a_ctds_ode"]["records"]
    unsat_recs = exp4["attack_a_ctds_ode"]["unsat_records"]

    all_labels = [f"{r['n']}" for r in sat_recs] + [f"{r['n']}" for r in unsat_recs]
    med_lna = [r["median_peak_ln_a"] for r in sat_recs] + [r["median_peak_ln_a"] for r in unsat_recs]
    max_lna = [r["max_peak_ln_a"] for r in sat_recs] + [r["max_peak_ln_a"] for r in unsat_recs]
    colors = [C_BLUE] * len(sat_recs) + [C_VERMILION] * len(unsat_recs)

    x = np.arange(len(all_labels))
    ax2.bar(x, med_lna, color=colors, edgecolor=C_DARK, linewidth=0.6, width=0.68, label="Median peak $\\ln a_m$")
    ax2.scatter(x, max_lna, color=C_DARK, s=22, zorder=5, label="Max trial $\\ln a_m$")

    for i, v in enumerate(med_lna):
        y_pos = v - 0.9 if v >= 3.0 else v - 0.65
        ax2.text(i, y_pos, f"{v:.1f}", ha="center", va="center", fontsize=6.5,
                 fontweight="bold", color="white")

    ax2.axvline(len(sat_recs) - 0.5, color=C_GRAY, linestyle="--", linewidth=1.0)
    ax2.text(1.5, 11.7, "Planted SAT\n(20/20 solved)", ha="center", va="center",
             fontsize=7.6, color=C_BLUE, fontweight="bold")
    ax2.text(5.0, 12.1, "Exact UNSAT\n(0/15 solved)", ha="center", va="center",
             fontsize=7.6, color=C_VERMILION, fontweight="bold")

    ax2.set_xticks(x)
    ax2.set_xticklabels(all_labels, fontsize=8.0)
    ax2.set_xlabel("Instance size (number of variables $n$)")
    ax2.set_ylabel(r"Peak Lagrange log-weight $\max_m \ln a_m(t)$")
    ax2.set_ylim(0, 14.8)
    ax2.set_title("(b) CTDS ODE (RK45 num. approx.)", fontsize=9.8)
    ax2.grid(True, axis="y", linestyle=":", alpha=0.4)
    ax2.legend(loc="upper left", fontsize=7.3, frameon=True, facecolor="white", framealpha=0.95)

    fig.text(
        0.01, -0.025,
        "Panel (a) codes: BLK = blocked/falsified by barrier; INS = bypasses barrier individually but algebraically insufficient; OPN = active open frontier.",
        fontsize=7.5, color=C_GRAY,
    )

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig4_wild_paths_barrier_matrix.pdf", bbox_inches="tight", metadata={"CreationDate": None})
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    make_fig4()
    print("Regenerated 4 crisp vector PDF figures in", FIG_DIR)


if __name__ == "__main__":
    main()
