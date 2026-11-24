# SPDX-License-Identifier: Apache-2.0
"""
Experiment 5: Characteristic-2 Permanent vs. Determinant Collapse &
Exact Mignon-Ressayre (2004) Hessian-Rank Determinantal Complexity Bound.

100% exact integer / rational arithmetic (zero floating-point operations).
"""

from __future__ import annotations

import itertools
import json
import math
import random
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = ROOT / "results"
RESULTS_DIR.mkdir(parents=True, exist_ok=True)


def exact_perm(M: list[list[int]]) -> int:
    """Exact permanent by definition (n <= 7)."""
    n = len(M)
    total = 0
    for p in itertools.permutations(range(n)):
        prod = 1
        for i in range(n):
            prod *= M[i][p[i]]
        total += prod
    return total


def perm_sign(p: tuple[int, ...]) -> int:
    inv = 0
    n = len(p)
    for i in range(n):
        for j in range(i + 1, n):
            if p[i] > p[j]:
                inv += 1
    return -1 if (inv & 1) else 1


def exact_det(M: list[list[int]]) -> int:
    """Exact determinant by Leibniz formula (n <= 7)."""
    n = len(M)
    total = 0
    for p in itertools.permutations(range(n)):
        prod = perm_sign(p)
        for i in range(n):
            prod *= M[i][p[i]]
        total += prod
    return total


def exact_rational_rank(mat: list[list[Fraction]]) -> int:
    """Exact rank over Q using Gaussian elimination with fractions.Fraction."""
    if not mat or not mat[0]:
        return 0
    A = [list(row) for row in mat]
    rows, cols = len(A), len(A[0])
    r = 0
    for c in range(cols):
        piv = -1
        for i in range(r, rows):
            if A[i][c] != 0:
                piv = i
                break
        if piv == -1:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = Fraction(1, 1) / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                factor = A[i][c]
                A[i] = [A[i][j] - factor * A[r][j] for j in range(cols)]
        r += 1
    return r


def mignon_ressayre_hessian_rank(n: int) -> dict:
    """
    Mignon-Ressayre (2004): At the point A_0 with first row (1,0,...,0) and
    submatrix (rows 1..n-1, cols 1..n-1) = J_{n-1} (or standard MR point A_0 where
    Perm(A_0) = 0 and Hessian has rank n^2 - 2n + 2? Actually at A_0 = [[0, 1,...,1],[1,0,...,0],...],
    let's compute the exact Hessian H_{(i,j),(k,l)} = d^2 Perm_n / (dx_{i,j} dx_{k,l}) at
    the exact Mignon-Ressayre singular point A_0:
      A_0[0][0] = -(n-1)  (or 1 - n),  all other entries = 1!
      Check: Perm_n(A_0) = (1-n)*(n-1)! + (n-1)*(n-1)! = 0 !!
    And the (n^2 x n^2) Hessian H at A_0 has exact rank n^2 (or n^2 - ...), giving dc(Perm_n) >= rank(H)/2 = n^2/2!
    Let's compute the EXACT rational rank of H(Perm_n) at A_0!
    """
    A0 = [[1 for _ in range(n)] for _ in range(n)]
    A0[0][0] = 1 - n
    p_val = exact_perm(A0)
    assert p_val == 0, f"Expected Perm(A0)=0, got {p_val}"

    # Second partial derivative d^2 Perm / (dx_{i,j} dx_{k,l}) at A0:
    # = 0 if i == k or j == l
    # = Perm(A0 with rows {i,k} and cols {j,l} removed) otherwise!
    coords = [(i, j) for i in range(n) for j in range(n)]
    N2 = n * n
    H: list[list[Fraction]] = [[Fraction(0) for _ in range(N2)] for _ in range(N2)]
    for idx1, (i, j) in enumerate(coords):
        for idx2, (k, l) in enumerate(coords):
            if i == k or j == l:
                continue
            sub = [
                [A0[r][c] for c in range(n) if c != j and c != l]
                for r in range(n) if r != i and r != k
            ]
            val = 1 if len(sub) == 0 else exact_perm(sub)
            H[idx1][idx2] = Fraction(val)

    rk = exact_rational_rank(H)
    mr_lower_bound = math.ceil(rk / 2)
    return {
        "n": n,
        "A0_00": 1 - n,
        "perm_at_A0": p_val,
        "hessian_dim": N2,
        "exact_hessian_rank_over_Q": rk,
        "mignon_ressayre_dc_lower_bound_ceil_rk_div_2": mr_lower_bound,
        "n_squared_div_2": (n * n) / 2,
    }


def main() -> None:
    print("=== Experiment 5: Char-2 Perm/Det Collapse & Exact Mignon-Ressayre Hessian Rank ===")
    rng = random.Random(20261123)

    char2_checks = []
    for n in [2, 3, 4, 5]:
        trials = 16 if n == 2 else (64 if n == 3 else 40)
        mismatches_mod2 = 0
        # Witness matrix with Perm != Det over Z AND over F_3:
        # Block diag([[1,1],[1,1]], I_{n-2}) has Perm = 2, Det = 0!
        W = [[0] * n for _ in range(n)]
        W[0][0] = W[0][1] = W[1][0] = W[1][1] = 1
        for i in range(2, n):
            W[i][i] = 1
        pw, dw = exact_perm(W), exact_det(W)
        assert pw == 2 and dw == 0 and (pw % 3) != (dw % 3)

        # Also all-ones J_n: Perm = n!, Det = 0
        J = [[1] * n for _ in range(n)]
        pj, dj = exact_perm(J), exact_det(J)
        assert pj == math.factorial(n) and dj == 0

        for _ in range(trials):
            M = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(n)]
            if (exact_perm(M) - exact_det(M)) % 2 != 0:
                mismatches_mod2 += 1
        assert mismatches_mod2 == 0
        char2_checks.append({
            "n": n,
            "random_int_matrices_tested": trials,
            "char2_mismatches": mismatches_mod2,
            "J_n_perm": pj,
            "J_n_det": dj,
            "W_n_perm_mod3": pw % 3,
            "W_n_det_mod3": dw % 3,
        })
        print(
            f"  n={n}: char2 mismatches=0/{trials}, Perm(J_n)={pj} vs Det(J_n)={dj}, "
            f"W_n mod 3: Perm={pw%3} != Det={dw%3}"
        )

    mr_checks = []
    for n in [2, 3, 4, 5]:
        mr = mignon_ressayre_hessian_rank(n)
        mr_checks.append(mr)
        print(
            f"  Mignon-Ressayre n={n}: Perm(A0)={mr['perm_at_A0']}, "
            f"exact Hessian rank={mr['exact_hessian_rank_over_Q']}/{mr['hessian_dim']} "
            f"=> dc(Perm_{n}) >= {mr['mignon_ressayre_dc_lower_bound_ceil_rk_div_2']}"
        )

    out_path = RESULTS_DIR / "exp5_char2_and_hessian.json"
    out_path.write_text(
        json.dumps(
            {
                "experiment": "exp5_char2_collapse_and_mignon_ressayre",
                "arithmetic": "exact_integer_rational",
                "char2_collapse": char2_checks,
                "mignon_ressayre_hessian": mr_checks,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"\nSaved exact results to {out_path}")


if __name__ == "__main__":
    main()
