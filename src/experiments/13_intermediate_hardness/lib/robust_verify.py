"""
Robust stress verification for Experiment 13.

This script complements verify.py and deep_verify.py with larger randomized
coverage (deterministic via fixed seeds) and worst-case linearized checks.
"""

import math
import random
from itertools import combinations


def check_phase_scaling_random(trials=250, seed=1301):
    """Randomized exponent checks for Proposition 8 core scaling laws."""
    rng = random.Random(seed)

    for _ in range(trials):
        n = rng.randint(24, 180)
        c = rng.uniform(0.05, 0.95)
        eps = 2.0 ** (-c * n)
        q = 1.0 / eps
        cval = 1.0 / (eps * eps)
        sep = cval / q

        assert abs(math.log2(q) / n - c) < 1e-10
        assert abs(math.log2(cval) / n - 2.0 * c) < 1e-10
        assert abs(math.log2(sep) / n - c) < 1e-10


def _worst_case_rounding_error(n, deltas):
    """
    Compute the worst-case (adversarial-sign) linearized rounding error bound
    for one interpolation instance, following the theorem-1 chain.
    """
    M = len(deltas)
    N = float(2**n)
    eps = 2.0 ** (-n / 2.0)
    nodes = [2 * j + 1 for j in range(M)]

    sample_err_bound = []
    for xj in nodes:
        prod = 1.0
        for d in deltas:
            prod *= (d + xj / 2.0)
        sample_err_bound.append(3.0 * eps * prod)

    max_err = 0.0
    for k, dk in enumerate(deltas):
        denom = 1.0
        for ell, de in enumerate(deltas):
            if ell != k:
                denom *= abs(de - dk)
        if denom == 0.0:
            return math.inf

        x_star = -2.0 * dk
        acc = 0.0
        for j, xj in enumerate(nodes):
            lag_abs = 1.0
            for i, xi in enumerate(nodes):
                if i != j:
                    lag_abs *= abs((x_star - xi) / (xj - xi))
            acc += sample_err_bound[j] * lag_abs

        err_k = (N / denom) * acc
        max_err = max(max_err, err_k)

    return max_err


def check_interpolation_barrier_random(trials=180, seed=1302):
    """
    Randomized worst-case interpolation-barrier checks.
    For each random integer-gap instance, confirm existence of admissible
    oracle perturbations causing rounding failure at eps = 2^{-n/2}.
    """
    rng = random.Random(seed)
    failures = 0

    for _ in range(trials):
        n = rng.randint(8, 24)
        M = rng.randint(3, min(8, n))
        max_gap = 6 * M + 3

        nonzero = rng.sample(list(range(1, max_gap + 1)), M - 1)
        deltas = [0] + sorted(nonzero)
        worst_err = _worst_case_rounding_error(n, deltas)

        if worst_err > 0.5:
            failures += 1

    # We expect the barrier to be overwhelmingly active in this range.
    assert failures >= int(0.95 * trials), (
        f"Barrier check weaker than expected: {failures}/{trials} failures"
    )


def check_interpolation_barrier_exhaustive_small():
    """
    Exhaustive small-parameter verification for interpolation barrier:
    iterate through all distinct integer-gap sets in a fixed small regime and
    confirm worst-case rounding failure at eps = 2^{-n/2}.
    """
    total = 0

    for n in [4, 6, 8, 10]:
        for M in [3, 4, 5]:
            max_gap = 2 * M + 2
            for comb in combinations(range(1, max_gap + 1), M - 1):
                deltas = [0] + list(comb)
                worst_err = _worst_case_rounding_error(n, deltas)
                assert worst_err > 0.5, (
                    f"Exhaustive barrier failure missing at n={n}, M={M}, "
                    f"deltas={deltas}, worst_err={worst_err}"
                )
                total += 1

    return total


def check_structure_irrelevance_random(trials=250, seed=1303):
    """
    Randomized asymptotic checks for theorem-7 style higher-level suppression.
    """
    rng = random.Random(seed)

    for _ in range(trials):
        n = rng.randint(16, 40)
        M = rng.randint(3, 8)
        N = float(2**n)
        eps = 2.0 ** (-n / 2.0)

        # Canonical higher-level term for gaps [1,2,...,M-1]:
        # C = sum_{k=2}^{M-1} 1/k
        C = sum(1.0 / k for k in range(2, M))
        ratio = (C / N) / eps

        assert ratio < 0.05, (
            f"Higher-level term not negligible: n={n}, M={M}, ratio={ratio}"
        )


def check_threshold_separation_random(trials=160, seed=1304):
    """Randomized threshold checks: Q=2^{n/2}, C=2^n, ratio=2^{n/2}."""
    rng = random.Random(seed)

    for _ in range(trials):
        n = 2 * rng.randint(4, 40)  # even n for exact n/2 exponent
        eps = 2.0 ** (-n / 2.0)
        q = 1.0 / eps
        cval = 1.0 / (eps * eps)
        ratio = cval / q

        assert abs(q - (2.0 ** (n / 2.0))) < 1e-9
        assert abs(cval - (2.0**n)) < 1e-3
        assert abs(ratio - (2.0 ** (n / 2.0))) < 1e-9


if __name__ == "__main__":
    print("Experiment 13: Robust Stress Verification\n")

    check_phase_scaling_random()
    print("[PASS] Randomized phase-scaling exponent checks")

    check_interpolation_barrier_random()
    print("[PASS] Randomized interpolation-barrier worst-case checks")

    total = check_interpolation_barrier_exhaustive_small()
    print(f"[PASS] Exhaustive small-parameter barrier checks ({total} instances)")

    check_structure_irrelevance_random()
    print("[PASS] Randomized higher-level suppression checks")

    check_threshold_separation_random()
    print("[PASS] Randomized threshold separation checks")

    print("\nALL ROBUST CHECKS PASSED")
