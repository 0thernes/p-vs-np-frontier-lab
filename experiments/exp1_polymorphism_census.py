# SPDX-License-Identifier: Apache-2.0
"""
Experiment 1: Exact Universal-Algebraic Polymorphism Census &
Sheaf-Contextuality vs. Tractability (XOR-SAT / Mermin-Peres / Tseitin) Benchmark.

All algebraic checks use exact integer/Boolean arithmetic (zero floats).
CDCL solver measurements invoke CaDiCaL 2.1.2 directly and parse exact conflict/decision counts.
"""

from __future__ import annotations

import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = ROOT / "results"
RESULTS_DIR.mkdir(parents=True, exist_ok=True)


def resolve_cadical_bin() -> Path:
    """Resolve CaDiCaL binary cross-platform without hardcoded usernames."""
    env_bin = os.environ.get("CADICAL_BIN")
    if env_bin:
        p = Path(env_bin)
        if p.is_file():
            return p
    which = shutil.which("cadical")
    if which:
        return Path(which)
    exe = "cadical.exe" if sys.platform == "win32" else "cadical"
    pinned = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.35.0" / "bin" / exe
    if pinned.is_file():
        return pinned
    elan_tc = Path.home() / ".elan" / "toolchains"
    if elan_tc.is_dir():
        for cand in sorted(elan_tc.glob(f"*/bin/{exe}"), reverse=True):
            if cand.is_file():
                return cand
    return pinned


CADICAL_BIN = resolve_cadical_bin()


# ---------------------------------------------------------------------------
# Part A: Exhaustive Polymorphism Clone Census (arities 1, 2, 3)
# ---------------------------------------------------------------------------

def all_tuples(arity: int) -> list[tuple[int, ...]]:
    return list(itertools.product((0, 1), repeat=arity))


def clause_rel(forbidden: tuple[int, ...]) -> frozenset[tuple[int, ...]]:
    return frozenset(t for t in all_tuples(len(forbidden)) if t != forbidden)


RELATIONS: dict[str, frozenset[tuple[int, ...]]] = {
    "R000": clause_rel((0, 0, 0)),  # x v y v z
    "R001": clause_rel((0, 0, 1)),  # x v y v ~z
    "R011": clause_rel((0, 1, 1)),  # x v ~y v ~z
    "R111": clause_rel((1, 1, 1)),  # ~x v ~y v ~z
    "NAE3": frozenset(t for t in all_tuples(3) if t not in {(0, 0, 0), (1, 1, 1)}),
    "1in3": frozenset({(1, 0, 0), (0, 1, 0), (0, 0, 1)}),
    "XOR3_even": frozenset(t for t in all_tuples(3) if (t[0] ^ t[1] ^ t[2]) == 0),
    "XOR3_odd": frozenset(t for t in all_tuples(3) if (t[0] ^ t[1] ^ t[2]) == 1),
    "2SAT_00": clause_rel((0, 0)),
    "2SAT_01": clause_rel((0, 1)),
    "2SAT_11": clause_rel((1, 1)),
}


def preserves_relation(op_tt: int, arity: int, rel: frozenset[tuple[int, ...]]) -> bool:
    """Return True iff Boolean op with truth-table bitmask op_tt preserves rel."""
    rel_list = list(rel)
    k = len(rel_list[0])
    for tup_choice in itertools.product(rel_list, repeat=arity):
        out = []
        for coord in range(k):
            idx = 0
            for j in range(arity):
                idx = (idx << 1) | tup_choice[j][coord]
            out.append((op_tt >> idx) & 1)
        if tuple(out) not in rel:
            return False
    return True


def projection_bitmasks(arity: int) -> set[int]:
    """Truth-table bitmasks of the `arity` projection functions p_j(x) = x_j."""
    n_inputs = 1 << arity
    projs = set()
    for j in range(arity):
        mask = 0
        for idx in range(n_inputs):
            bit = (idx >> (arity - 1 - j)) & 1
            if bit:
                mask |= (1 << idx)
        projs.add(mask)
    return projs


def name_ternary_op(tt: int) -> str:
    known = {
        0b00000000: "const_0",
        0b11111111: "const_1",
        0b11110000: "proj_0",
        0b11001100: "proj_1",
        0b10101010: "proj_2",
        0b00001111: "not_0",
        0b00110011: "not_1",
        0b01010101: "not_2",
        0b10010110: "x^y^z (Maltsev)",
        0b01101001: "x^y^z^1 (dual-Maltsev)",
        0b11101000: "maj(x,y,z)",
        0b00010111: "~maj(x,y,z)",
        0b10000000: "x&y&z",
        0b11111110: "x|y|z",
    }
    return known.get(tt, f"op3_0x{tt:02x}")


def run_polymorphism_census() -> dict:
    clause_names = ["R000", "R001", "R011", "R111"]
    projs3 = projection_bitmasks(3)
    projs2 = projection_bitmasks(2)
    projs1 = projection_bitmasks(1)

    subset_results = []
    for r in range(1, 5):
        for comb in itertools.combinations(clause_names, r):
            rels = [RELATIONS[name] for name in comb]
            ops1 = [tt for tt in range(4) if all(preserves_relation(tt, 1, R) for R in rels)]
            ops2 = [tt for tt in range(16) if all(preserves_relation(tt, 2, R) for R in rels)]
            ops3 = [tt for tt in range(256) if all(preserves_relation(tt, 3, R) for R in rels)]
            only_proj3 = set(ops3) == projs3
            subset_results.append({
                "subset": list(comb),
                "unary_count": len(ops1),
                "binary_count": len(ops2),
                "ternary_count": len(ops3),
                "only_projections_up_to_arity_3": (
                    set(ops1) == projs1 and set(ops2) == projs2 and only_proj3
                ),
                "sample_non_proj_ternary": [
                    name_ternary_op(tt) for tt in ops3 if tt not in projs3
                ][:6],
            })

    benchmark_families = {
        "XOR-3SAT (P, affine F2)": ["XOR3_even", "XOR3_odd"],
        "2-SAT (NL <= P, Bijunctive)": ["2SAT_00", "2SAT_01", "2SAT_11"],
        "Horn-3SAT (P, meet-semilattice)": ["R011", "R111"],
        "Dual-Horn-3SAT (P, join-semilattice)": ["R000", "R001"],
        "NAE-3SAT (NP-complete)": ["NAE3"],
        "1-in-3 SAT (NP-complete)": ["1in3"],
        "3-SAT minimal rigid triple {R000,R011,R111}": ["R000", "R011", "R111"],
        "Full 3-SAT {R000,R001,R011,R111}": ["R000", "R001", "R011", "R111"],
    }

    family_summary = {}
    for label, rnames in benchmark_families.items():
        rels = [RELATIONS[n] for n in rnames]
        ops3 = [tt for tt in range(256) if all(preserves_relation(tt, 3, R) for R in rels)]
        family_summary[label] = {
            "ternary_polymorphism_count": len(ops3),
            "only_projections_arity_3": set(ops3) == projs3,
            "has_maltsev_xor": (0b10010110 in ops3),
            "has_majority": (0b11101000 in ops3),
            "has_and3": (0b10000000 in ops3),
            "has_or3": (0b11111110 in ops3),
            "non_projection_examples": [name_ternary_op(tt) for tt in ops3 if tt not in projs3][:8],
        }

    return {
        "clause_subsets": subset_results,
        "csp_families": family_summary,
    }


# ---------------------------------------------------------------------------
# Part B: Exact F2 Gaussian Elimination, Maximal Contextuality & Tseitin CDCL
# ---------------------------------------------------------------------------

def solve_f2_linear(num_vars: int, equations: list[tuple[list[int], int]]) -> tuple[bool, int, list[int] | None]:
    """
    Exact Gaussian elimination over F2.
    Returns (is_sat, exact_row_operations, witness_assignment_or_None).
    """
    rows: list[int] = []
    for lhs_vars, rhs in equations:
        mask = 0
        for v in lhs_vars:
            mask ^= (1 << v)
        if rhs & 1:
            mask |= (1 << num_vars)
        rows.append(mask)

    row_ops = 0
    pivots: list[tuple[int, int]] = []
    r = 0
    m = len(rows)
    for col in range(num_vars):
        piv = -1
        for i in range(r, m):
            if (rows[i] >> col) & 1:
                piv = i
                break
        if piv == -1:
            continue
        if piv != r:
            rows[r], rows[piv] = rows[piv], rows[r]
            row_ops += 1
        for i in range(m):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
                row_ops += 1
        pivots.append((r, col))
        r += 1

    # Check consistency: 0 = 1 row?
    rhs_bit = 1 << num_vars
    for i in range(r, m):
        if rows[i] == rhs_bit:
            return False, row_ops, None

    # Construct exact witness assignment (free vars = 0)
    sol = [0] * num_vars
    for row_idx, col in pivots:
        sol[col] = (rows[row_idx] >> num_vars) & 1
    # Verify witness directly against original equations
    for lhs_vars, rhs in equations:
        val = 0
        for v in lhs_vars:
            val ^= sol[v]
        assert val == (rhs & 1), "F2 witness verification failed!"
    return True, row_ops, sol


def check_maximal_contextuality(num_vars: int, equations: list[tuple[list[int], int]]) -> dict:
    """
    Verify exact Abramsky-Brandenburger strong/maximal contextuality:
    full system has NO global section, while dropping ANY single equation admits a global section.
    """
    full_sat, ops_full, _ = solve_f2_linear(num_vars, equations)
    subset_sat_count = 0
    for drop_idx in range(len(equations)):
        sub = equations[:drop_idx] + equations[drop_idx + 1:]
        sat, _, _ = solve_f2_linear(num_vars, sub)
        if sat:
            subset_sat_count += 1
    return {
        "num_vars": num_vars,
        "num_equations": len(equations),
        "global_section_exists": full_sat,
        "proper_drop1_subsets_satisfiable": subset_sat_count,
        "maximally_contextual": (not full_sat) and (subset_sat_count == len(equations)),
        "f2_gaussian_row_ops": ops_full,
    }


def xor_eqs_to_cnf(num_vars: int, equations: list[tuple[list[int], int]]) -> list[list[int]]:
    """Exact CNF expansion of small-degree XOR equations (degree <= 4)."""
    clauses: list[list[int]] = []
    for lhs, rhs in equations:
        k = len(lhs)
        assert k <= 5
        for bits in itertools.product((0, 1), repeat=k):
            if (sum(bits) & 1) != (rhs & 1):
                # Forbid this assignment: literal is +(v+1) if bit==0 else -(v+1)
                clause = [(lhs[i] + 1) if bits[i] == 0 else -(lhs[i] + 1) for i in range(k)]
                clauses.append(clause)
    return clauses


def run_cadical_cnf(num_vars: int, clauses: list[list[int]], timeout_s: float = 15.0) -> dict:
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False, encoding="utf-8") as f:
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")
        cnf_path = f.name
    try:
        proc = subprocess.run(
            [str(CADICAL_BIN), cnf_path],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        out = proc.stdout + "\n" + proc.stderr
        status = "UNKNOWN"
        if "s UNSATISFIABLE" in out:
            status = "UNSAT"
        elif "s SATISFIABLE" in out:
            status = "SAT"
        m_conf = re.search(r"c\s+conflicts:\s+(\d+)", out)
        m_dec = re.search(r"c\s+decisions:\s+(\d+)", out)
        m_prop = re.search(r"c\s+propagations:\s+(\d+)", out)
        return {
            "status": status,
            "conflicts": int(m_conf.group(1)) if m_conf else None,
            "decisions": int(m_dec.group(1)) if m_dec else None,
            "propagations": int(m_prop.group(1)) if m_prop else None,
            "num_clauses": len(clauses),
        }
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "conflicts": None, "decisions": None, "num_clauses": len(clauses)}
    finally:
        try:
            os.remove(cnf_path)
        except OSError:
            pass


def build_mermin_peres() -> tuple[int, list[tuple[list[int], int]]]:
    """
    3x3 Mermin-Peres Magic Square:
    Variables 0..8 arranged in 3x3 grid.
    Rows 0,1,2 have parity 0; Cols 0,1 have parity 0; Col 2 has parity 1.
    """
    eqs = [
        ([0, 1, 2], 0),
        ([3, 4, 5], 0),
        ([6, 7, 8], 0),
        ([0, 3, 6], 0),
        ([1, 4, 7], 0),
        ([2, 5, 8], 1),
    ]
    return 9, eqs


def build_odd_cycle(n: int) -> tuple[int, list[tuple[list[int], int]]]:
    eqs = [([i, (i + 1) % n], 0 if i < n - 1 else 1) for i in range(n)]
    return n, eqs


def build_3regular_circulant_tseitin(n: int) -> tuple[int, list[tuple[list[int], int]]]:
    """
    Deterministic 3-regular connected circulant/Mobius-ladder graph on even n >= 4:
    edges (i, i+1 mod n) plus opposite chords (i, i + n/2) for i < n/2.
    Tseitin charge: vertex 0 has charge 1, all other vertices have charge 0 (odd total charge => UNSAT).
    """
    assert n >= 4 and n % 2 == 0
    edges: list[tuple[int, int]] = []
    inc: list[list[int]] = [[] for _ in range(n)]

    def add_edge(u: int, v: int) -> None:
        eid = len(edges)
        edges.append((u, v))
        inc[u].append(eid)
        inc[v].append(eid)

    for i in range(n):
        add_edge(i, (i + 1) % n)
    half = n // 2
    for i in range(half):
        add_edge(i, i + half)

    eqs = [(inc[v], 1 if v == 0 else 0) for v in range(n)]
    return len(edges), eqs


def build_pseudo_expander_3reg_tseitin(n: int, seed_step: int = 5) -> tuple[int, list[tuple[list[int], int]]]:
    """
    Deterministic 3-regular graph on even n >= 10 with twisted chord permutation
    (stronger expansion than Mobius ladder, driving exponential CDCL conflicts).
    """
    assert n >= 10 and n % 2 == 0
    edges: list[tuple[int, int]] = []
    inc: list[list[int]] = [[] for _ in range(n)]

    def add_edge(u: int, v: int) -> None:
        eid = len(edges)
        edges.append((u, v))
        inc[u].append(eid)
        inc[v].append(eid)

    for i in range(n):
        add_edge(i, (i + 1) % n)

    # Deterministic perfect matching of chord endpoints avoiding cycle edges
    half = n // 2
    # Pair i in 0..half-1 with half + ((3*i + 1) % half) if gcd(3, half)==1 else deterministic bijection
    stride = 3
    while stride < half and (half % stride == 0 or (stride > 1 and any(half % p == 0 and stride % p == 0 for p in range(2, stride + 1)))):
        stride += 2
    if stride >= half:
        stride = 1
    for i in range(half):
        u = 2 * i
        v = 2 * ((i * stride + half // 2) % half) + 1
        add_edge(u, v)

    eqs = [(inc[v], 1 if v == 0 else 0) for v in range(n)]
    return len(edges), eqs


def main() -> None:
    print("=== Experiment 1: Exact Polymorphism Census & Sheaf-Contextuality Benchmark ===")
    poly = run_polymorphism_census()

    print("\n[A] Minimal 3-SAT clause subsets forcing projection-only polymorphisms (arity <= 3):")
    for row in poly["clause_subsets"]:
        if row["only_projections_up_to_arity_3"]:
            print(f"  RIGID: {row['subset']} -> unary={row['unary_count']}, binary={row['binary_count']}, ternary={row['ternary_count']}")

    print("\n[B] CSP Families Ternary Polymorphism Count (out of 256):")
    for label, info in poly["csp_families"].items():
        print(
            f"  {label}: {info['ternary_polymorphism_count']} ops "
            f"(Maltsev={info['has_maltsev_xor']}, Maj={info['has_majority']}, "
            f"AND={info['has_and3']}, OR={info['has_or3']}, proj_only={info['only_projections_arity_3']})"
        )

    # Contextual XOR-SAT instances
    contextual_benchmarks = []

    # 1. Mermin-Peres Magic Square
    nv, eqs = build_mermin_peres()
    ctx = check_maximal_contextuality(nv, eqs)
    cnf = xor_eqs_to_cnf(nv, eqs)
    cdcl = run_cadical_cnf(nv, cnf)
    contextual_benchmarks.append({"name": "Mermin-Peres 3x3 Magic Square", **ctx, "cadical": cdcl})

    # 2. Odd Cycles C_3, C_5, C_7, C_11
    for n in [3, 5, 7, 11]:
        nv, eqs = build_odd_cycle(n)
        ctx = check_maximal_contextuality(nv, eqs)
        cnf = xor_eqs_to_cnf(nv, eqs)
        cdcl = run_cadical_cnf(nv, cnf)
        contextual_benchmarks.append({"name": f"Odd-Cycle C_{n}", **ctx, "cadical": cdcl})

    # 3. Tseitin 3-regular twisted-chord family (n = 10..46)
    tseitin_scaling = []
    for n in [10, 14, 18, 22, 26, 30, 34, 38, 42, 46]:
        nv, eqs = build_pseudo_expander_3reg_tseitin(n)
        ctx = check_maximal_contextuality(nv, eqs)
        cnf = xor_eqs_to_cnf(nv, eqs)
        cdcl = run_cadical_cnf(nv, cnf, timeout_s=15.0)
        row = {"vertices": n, "edges_vars": nv, **ctx, "cadical": cdcl}
        tseitin_scaling.append(row)
        print(
            f"  Tseitin(V={n:2d}, E={nv:2d}): max_ctx={ctx['maximally_contextual']}, "
            f"F2_Gauss_ops={ctx['f2_gaussian_row_ops']:4d}, "
            f"CaDiCaL={cdcl['status']} (conflicts={cdcl['conflicts']}, decisions={cdcl['decisions']})"
        )

    out = {
        "experiment": "exp1_polymorphism_census_and_sheaf_contextuality",
        "arithmetic": "exact_integer_boolean_f2",
        "polymorphism_census": poly,
        "contextual_benchmarks": contextual_benchmarks,
        "tseitin_3reg_scaling": tseitin_scaling,
    }
    out_path = RESULTS_DIR / "exp1_polymorphism_contextuality.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"\nSaved exact results to {out_path}")


if __name__ == "__main__":
    main()
