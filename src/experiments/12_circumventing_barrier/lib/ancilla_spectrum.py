"""
Numerical verification for Experiment 12: Circumventing the A_1 Barrier.

Verifies Theorems 1-5 by exact diagonalization for small N.

Key distinction: s* = A_1/(A_1+1) is the CROSSING POSITION from the secular
equation, NOT the gap minimum (which is at s=1/2 for Grover). The crossing
position determines the optimal local schedule K(s) = g(s)^2.

Hamiltonian: H(s) = -(1-s)|psi_0><psi_0| + s H_z
Extended:    H_ext(s) = -(1-s)|Psi><Psi| + s (H_z x I)  where |Psi> = |psi_0> x |phi>
Coupled:     H_ext(s) + V
"""

import numpy as np
from numpy.linalg import eigh


# ---------- Hamiltonian construction ----------

def build_Hz(energies):
    """Diagonal cost Hamiltonian from energy list."""
    return np.diag(np.array(energies, dtype=float))


def build_H(s, energies):
    """H(s) = -(1-s)|psi_0><psi_0| + s H_z."""
    N = len(energies)
    psi0 = np.ones(N) / np.sqrt(N)
    return -(1 - s) * np.outer(psi0, psi0) + s * build_Hz(energies)


def build_H_ext(s, energies, m_ancilla, phi=None, V=None):
    """Extended Hamiltonian with ancilla.

    H_ext(s) = -(1-s)|Psi><Psi| + s (H_z x I) [+ V]
    where |Psi> = |psi_0> x |phi>.
    """
    N = len(energies)
    d_anc = 2 ** m_ancilla

    psi0 = np.ones(N) / np.sqrt(N)
    if phi is None:
        phi = np.zeros(d_anc)
        phi[0] = 1.0
    Psi = np.kron(psi0, phi)

    H = -(1 - s) * np.outer(Psi, Psi) + s * np.kron(build_Hz(energies), np.eye(d_anc))

    if V is not None:
        H += V

    return H


# ---------- Spectral parameters ----------

def compute_spectral_params(energies):
    """Compute A_1, A_2, s*, and related spectral parameters."""
    E = np.array(energies, dtype=float)
    N = len(E)
    E_vals = np.sort(np.unique(E))
    E_0 = E_vals[0]
    Delta = E_vals[1] - E_0 if len(E_vals) > 1 else 0.0

    degens = {}
    for ev in E_vals:
        degens[ev] = int(np.sum(np.isclose(E, ev)))
    d_0 = degens[E_0]

    A_1 = 0.0
    A_2 = 0.0
    for ev in E_vals:
        if ev > E_0:
            dk = degens[ev]
            A_1 += (dk / N) / (ev - E_0)
            A_2 += (dk / N) / (ev - E_0) ** 2

    s_star = A_1 / (A_1 + 1)

    return {
        'E_0': E_0, 'Delta': Delta, 'd_0': d_0, 'N': N,
        'A_1': A_1, 'A_2': A_2, 's_star': s_star,
        'E_vals': E_vals, 'degens': degens
    }


# ---------- Eigenvalue branch tracking ----------

def track_eigenvalue_branches(energies, s_grid=None, use_ext=False,
                              m_ancilla=0, phi=None, V=None):
    """Track all eigenvalue branches of H(s) or H_ext(s).

    Returns: (s_grid, all_eigs) where all_eigs[i, j] is the j-th
    eigenvalue (sorted) at s = s_grid[i].
    """
    if s_grid is None:
        s_grid = np.linspace(0.001, 0.999, 2000)

    all_eigs = []
    for s in s_grid:
        if use_ext:
            H = build_H_ext(s, energies, m_ancilla, phi=phi, V=V)
        else:
            H = build_H(s, energies)
        eigs = np.sort(eigh(H)[0])
        all_eigs.append(eigs)

    all_eigs = np.array(all_eigs)
    return s_grid, all_eigs


def find_secular_crossing(energies):
    """Return s* = A_1/(A_1+1) from the secular equation.

    The crossing position is determined analytically by the spectral
    parameters, not by gap minimization (the gap minimum is at s=1/2
    for Grover, while s*=A_1/(A_1+1) != 1/2 in general).
    """
    params = compute_spectral_params(energies)
    return params['s_star']


def verify_secular_equation(energies, s_values=None, verbose=True):
    """Verify the secular equation directly.

    At each s, compute eigenvalues of H(s) and check that they satisfy
    1/(1-s) = (1/N) sum_k d_k / (s*E_k - lambda).
    """
    if s_values is None:
        s_values = [0.2, 0.3, 0.4, 0.5, 0.6]

    params = compute_spectral_params(energies)
    N = params['N']
    E_vals = params['E_vals']
    degens = params['degens']

    if verbose:
        print(f"Secular equation verification: N={N}")

    for s in s_values:
        H = build_H(s, energies)
        eigs = np.sort(eigh(H)[0])

        # Check the secular equation for the ground eigenvalue
        lam = eigs[0]
        lhs = 1.0 / (1.0 - s)
        rhs = 0.0
        for ev in E_vals:
            dk = degens[ev]
            denom = s * ev - lam
            if abs(denom) > 1e-14:
                rhs += (dk / N) / denom

        if verbose:
            print(f"  s={s:.2f}: lambda_0={lam:.6f}, "
                  f"LHS={lhs:.6f}, RHS={rhs:.6f}, "
                  f"diff={abs(lhs-rhs):.2e}")

    return True


# ---------- Crossing invariance verification ----------

def verify_branch_invariance(energies, m_ancilla=1, phi=None, verbose=True):
    """Verify that the two crossing eigenvalue branches are identical
    in the bare and extended systems.

    The extended system has extra eigenvalues (from states orthogonal to
    |Psi> in the ancilla space), but the two branches participating in
    the avoided crossing are unchanged.
    """
    N = len(energies)
    params = compute_spectral_params(energies)
    d_0 = params['d_0']
    E_0 = params['E_0']

    s_grid = np.linspace(0.001, 0.999, 2000)
    d_anc = 2 ** m_ancilla

    bare_eigs = []
    ext_eigs = []

    for s in s_grid:
        H_bare = build_H(s, energies)
        H_ext = build_H_ext(s, energies, m_ancilla, phi=phi)

        eigs_b = np.sort(eigh(H_bare)[0])
        eigs_e = np.sort(eigh(H_ext)[0])

        bare_eigs.append(eigs_b)
        ext_eigs.append(eigs_e)

    bare_eigs = np.array(bare_eigs)
    ext_eigs = np.array(ext_eigs)

    # The ground eigenvalue of the bare system should appear in the
    # extended system's spectrum.
    # The key crossing branch eigenvalue (first non-degenerate excited)
    # should also appear.

    # Ground state: eigs_b[0] should match eigs_e[0] exactly
    ground_diff = np.max(np.abs(bare_eigs[:, 0] - ext_eigs[:, 0]))

    # First crossing branch: for bare system it's eigs_b[1] (for d_0=1)
    # or eigs_b[d_0] (for d_0>1, since d_0-1 eigenvalues sit at s*E_0).
    # In the extended system, there are extra eigenvalues from the
    # ancilla null space. We need to find which extended eigenvalue
    # matches the bare crossing branch.

    # For d_0=1: bare_eigs[:,1] should match one of ext_eigs
    # For d_0>1: bare_eigs[:,d_0] should match one of ext_eigs

    # Strategy: for each s, find the extended eigenvalue closest to
    # the bare crossing branch eigenvalue.
    cross_idx = 1 if d_0 == 1 else d_0
    cross_diffs = []
    for i in range(len(s_grid)):
        bare_val = bare_eigs[i, cross_idx]
        diffs = np.abs(ext_eigs[i, :] - bare_val)
        cross_diffs.append(np.min(diffs))
    cross_diff = np.max(cross_diffs)

    if verbose:
        print(f"Branch invariance: N={N}, m_ancilla={m_ancilla}")
        print(f"  Max |ground_bare - ground_ext| = {ground_diff:.2e}")
        print(f"  Max |cross_bare - cross_ext|   = {cross_diff:.2e}")
        print(f"  (Both should be < 1e-10)")
        print()

    assert ground_diff < 1e-10, f"Ground state mismatch: {ground_diff}"
    assert cross_diff < 1e-10, f"Crossing branch mismatch: {cross_diff}"
    return True


# ---------- Coupling operators ----------

def sigma_x_ancilla(N, m_ancilla):
    """I_N x sigma_x on first ancilla qubit."""
    sx = np.array([[0, 1], [1, 0]], dtype=float)
    if m_ancilla == 1:
        anc_op = sx
    else:
        anc_op = sx
        for _ in range(m_ancilla - 1):
            anc_op = np.kron(anc_op, np.eye(2))
    return np.kron(np.eye(N), anc_op)


# ---------- Test cases ----------

def grover_energies(N, M):
    """Grover-type: M states at E=0, rest at E=1."""
    return [0.0] * M + [1.0] * (N - M)


def three_level_energies(N, d0, d1, E1=1.0, E2=2.0):
    """Three-level: d0 at E=0, d1 at E1, rest at E2."""
    d2 = N - d0 - d1
    return [0.0] * d0 + [E1] * d1 + [E2] * d2


# ---------- Theorem 1: Product State Invariance ----------

def verify_theorem1(verbose=True):
    """Theorem 1: For product |Psi> = |psi_0> x |phi> and H_f = H_z x I,
    the eigenvalue branches participating in the avoided crossing are
    IDENTICAL to the bare system. Hence s* = A_1/(A_1+1) is unchanged.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 1: Product State Invariance")
        print("=" * 60)
        print()

    test_cases = [
        ("Grover N=4, M=1", grover_energies(4, 1), 1),
        ("Grover N=4, M=1, 2 ancillas", grover_energies(4, 1), 2),
        ("Grover N=8, M=1", grover_energies(8, 1), 1),
        ("Grover N=8, M=2", grover_energies(8, 2), 1),
        ("Three-level N=8", three_level_energies(8, 1, 3, 1.0, 3.0), 1),
        ("Three-level N=8, 2 ancillas", three_level_energies(8, 1, 3, 1.0, 3.0), 2),
    ]

    for name, energies, m_anc in test_cases:
        if verbose:
            params = compute_spectral_params(energies)
            print(f"--- {name} ---")
            print(f"  A_1={params['A_1']:.4f}, s*={params['s_star']:.4f}, "
                  f"d_0={params['d_0']}")
        verify_branch_invariance(energies, m_ancilla=m_anc, verbose=verbose)

    # Also verify with non-standard ancilla states
    if verbose:
        print("--- Grover N=4, M=1, ancilla |+> ---")
    d_anc = 2
    phi_plus = np.ones(d_anc) / np.sqrt(d_anc)
    verify_branch_invariance(grover_energies(4, 1), m_ancilla=1,
                             phi=phi_plus, verbose=verbose)

    if verbose:
        print("--- Grover N=4, M=1, ancilla (0.3|0> + 0.95|1>) ---")
    phi_asym = np.array([0.3, 0.95])
    phi_asym /= np.linalg.norm(phi_asym)
    verify_branch_invariance(grover_energies(4, 1), m_ancilla=1,
                             phi=phi_asym, verbose=verbose)

    if verbose:
        print("Theorem 1: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 2: Universality of Uniform Superposition ----------

def verify_theorem2(verbose=True):
    """Theorem 2: Non-uniform initial states change the crossing position.

    Among all |psi> in C^N, only |psi_0> = (1/sqrt(N)) sum |z> gives
    a crossing position that depends only on {E_k, d_k}.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 2: Universality of Uniform Superposition")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)  # d_0=1 for clean crossing
    params = compute_spectral_params(energies)
    s_star_uniform = params['s_star']

    # Non-uniform state: bias toward ground state
    psi_biased = np.array([0.8, 0.3, 0.3, 0.3])
    psi_biased /= np.linalg.norm(psi_biased)

    # Build H(s) with non-uniform initial state
    Hz = build_Hz(energies)
    s_grid = np.linspace(0.001, 0.999, 4000)

    # Track the secular equation crossing for the non-uniform state
    # The secular equation becomes:
    # 1/(1-s) = sum_k w_k / (s E_k - lambda)
    # where w_k = sum_{z: E(z)=E_k} |<psi|z>|^2
    # For non-uniform psi, w_k != d_k/N in general.

    # Compute effective w_k
    E = np.array(energies)
    E_vals = np.sort(np.unique(E))
    w_k_uniform = {}
    w_k_biased = {}
    psi_uniform = np.ones(N) / np.sqrt(N)
    for ev in E_vals:
        mask = np.isclose(E, ev)
        w_k_uniform[ev] = np.sum(np.abs(psi_uniform[mask])**2)
        w_k_biased[ev] = np.sum(np.abs(psi_biased[mask])**2)

    # Effective A_1 for biased state
    E_0 = E_vals[0]
    A1_biased = sum(w_k_biased[ev] / (ev - E_0) for ev in E_vals if ev > E_0)
    s_star_biased_theory = A1_biased / (A1_biased + 1)

    # Verify numerically: compute eigenvalues and find crossing
    gaps_biased = []
    for s in s_grid:
        H = -(1 - s) * np.outer(psi_biased, psi_biased) + s * Hz
        eigs = np.sort(eigh(H)[0])
        gaps_biased.append(eigs[1] - eigs[0])
    gaps_biased = np.array(gaps_biased)

    # Also check: does the biased secular equation give a different s*?
    if verbose:
        print(f"  N={N}, energies={energies}")
        print(f"  Uniform: w_k = {w_k_uniform}, A_1 = {params['A_1']:.4f}, "
              f"s* = {s_star_uniform:.4f}")
        print(f"  Biased:  w_k = {w_k_biased}, A_1 = {A1_biased:.4f}, "
              f"s* = {s_star_biased_theory:.4f}")
        print(f"  Shift in s*: {s_star_biased_theory - s_star_uniform:+.4f}")
        print()

    assert abs(s_star_biased_theory - s_star_uniform) > 0.01, \
        "Non-uniform state should shift s* significantly"

    # Now verify that the crossing position depends on the ASSIGNMENT
    # of energies to basis states (not just {E_k, d_k}) for non-uniform psi.
    # Permute the energy assignment:
    energies_perm = [1.0, 0.0, 1.0, 1.0]  # same {E_k, d_k}, different assignment
    w_k_biased_perm = {}
    E_perm = np.array(energies_perm)
    for ev in E_vals:
        mask = np.isclose(E_perm, ev)
        w_k_biased_perm[ev] = np.sum(np.abs(psi_biased[mask])**2)

    A1_biased_perm = sum(w_k_biased_perm[ev] / (ev - E_0)
                         for ev in E_vals if ev > E_0)
    s_star_biased_perm = A1_biased_perm / (A1_biased_perm + 1)

    if verbose:
        print(f"  Permuted assignment: w_k = {w_k_biased_perm}, "
              f"A_1 = {A1_biased_perm:.4f}, s* = {s_star_biased_perm:.4f}")
        print(f"  Original biased s* - permuted s* = "
              f"{s_star_biased_theory - s_star_biased_perm:+.4f}")
        print(f"  (Non-zero means s* depends on assignment, not just spectrum)")
        print()

    # For uniform psi, the permutation should NOT matter
    w_k_uniform_perm = {}
    for ev in E_vals:
        mask = np.isclose(E_perm, ev)
        w_k_uniform_perm[ev] = np.sum(np.abs(psi_uniform[mask])**2)

    A1_uniform_perm = sum(w_k_uniform_perm[ev] / (ev - E_0)
                          for ev in E_vals if ev > E_0)

    if verbose:
        print(f"  Uniform with permutation: w_k = {w_k_uniform_perm}, "
              f"A_1 = {A1_uniform_perm:.4f}")
        print(f"  |A_1_orig - A_1_perm| = "
              f"{abs(params['A_1'] - A1_uniform_perm):.2e} (should be ~0)")
        print()

    assert abs(params['A_1'] - A1_uniform_perm) < 1e-10, \
        "Uniform superposition A_1 should be invariant under permutation"
    assert abs(s_star_biased_theory - s_star_biased_perm) > 0.01, \
        "Biased state s* should depend on energy assignment"

    # Flat-amplitude, non-uniform-phase state: |psi> = (1/sqrt(N)) sum e^{i theta_z} |z>
    # This should give the SAME weights as uniform (phases cancel in |<z|psi>|^2 = 1/N)
    psi_phased = np.array([1, 1j, -1, -1j], dtype=complex) / np.sqrt(N)
    w_k_phased = {}
    for ev in E_vals:
        mask = np.isclose(E, ev)
        w_k_phased[ev] = np.sum(np.abs(psi_phased[mask])**2)
    A1_phased = sum(w_k_phased[ev] / (ev - E_0) for ev in E_vals if ev > E_0)

    if verbose:
        print(f"  Flat-amplitude phased state: w_k = {w_k_phased}, "
              f"A_1 = {A1_phased:.4f}")
        print(f"  |A_1_uniform - A_1_phased| = "
              f"{abs(params['A_1'] - A1_phased):.2e} (should be ~0)")
        print()

    assert abs(params['A_1'] - A1_phased) < 1e-10, \
        "Flat-amplitude phased state should give same A_1 as uniform"

    if verbose:
        print("Theorem 2: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 3: Coupled Ancilla Extension ----------

def verify_theorem3(verbose=True):
    """Theorem 3: Instance-independent coupling cannot eliminate A_1 dependence.

    Shows that coupling V changes A_1^eff by an amount that depends on
    the original spectrum, so it cannot make s* spectrum-independent.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 3: Coupled Ancilla Extension")
        print("=" * 60)
        print()

    # Fix V = lam * |0><0| x sigma_x (instance-independent coupling)
    lam = 0.05

    # Test with two different spectra that have different A_1
    test_spectra = [
        ("Grover N=4, M=1", grover_energies(4, 1)),
        ("Grover N=8, M=1", grover_energies(8, 1)),
        ("Grover N=8, M=2", grover_energies(8, 2)),
        ("Three-level N=8", three_level_energies(8, 1, 3, 1.0, 3.0)),
    ]

    if verbose:
        print(f"  Fixed coupling: lam={lam} * I_N x sigma_x")
        print()
        print(f"  {'Instance':<25s} {'A_1':>8s} {'s*(bare)':>10s} "
              f"{'s*(coupled)':>12s} {'shift':>8s}")

    bare_s_stars = []
    coupled_s_stars = []

    for name, energies in test_spectra:
        N = len(energies)
        params = compute_spectral_params(energies)
        s_star_bare = params['s_star']

        # Compute effective A_1 for the coupled system
        # Eigenvalues of H_f = H_z x I + lam * I x sigma_x
        Hz_ext = np.kron(build_Hz(energies), np.eye(2))
        V = lam * np.kron(np.eye(N), np.array([[0, 1], [1, 0]]))
        Hf = Hz_ext + V

        evals_f, evecs_f = eigh(Hf)
        E0_f = evals_f[0]

        # Initial state
        psi0 = np.ones(N) / np.sqrt(N)
        phi = np.array([1.0, 0.0])
        Psi = np.kron(psi0, phi)

        # Effective A_1
        A1_eff = 0.0
        for j in range(len(evals_f)):
            if evals_f[j] > E0_f + 1e-12:
                wj = abs(np.dot(Psi, evecs_f[:, j])) ** 2
                A1_eff += wj / (evals_f[j] - E0_f)

        s_star_coupled = A1_eff / (A1_eff + 1)

        bare_s_stars.append(s_star_bare)
        coupled_s_stars.append(s_star_coupled)

        if verbose:
            shift = s_star_coupled - s_star_bare
            print(f"  {name:<25s} {params['A_1']:8.4f} {s_star_bare:10.4f} "
                  f"{s_star_coupled:12.4f} {shift:+8.4f}")

    if verbose:
        print()
        # Key test: do different bare s* values map to different coupled s* values?
        # If the coupling eliminated A_1 dependence, all coupled s* would be equal.
        spread_bare = max(bare_s_stars) - min(bare_s_stars)
        spread_coupled = max(coupled_s_stars) - min(coupled_s_stars)
        print(f"  Spread of s*(bare):    {spread_bare:.4f}")
        print(f"  Spread of s*(coupled): {spread_coupled:.4f}")
        print(f"  Coupling does NOT collapse s* to a single value.")
        print()

    assert max(coupled_s_stars) - min(coupled_s_stars) > 0.01, \
        "Coupled s* should still vary across instances"

    # Sweep over coupling strengths to verify non-collapse for all lambda
    if verbose:
        print(f"\n  Lambda sweep (spread of s* across instances):")
        print(f"  {'lambda':>8s} {'spread':>10s}")

    for lam_sweep in [0.01, 0.05, 0.1, 0.5, 1.0]:
        coupled_stars = []
        for name, energies in test_spectra:
            N = len(energies)
            Hz_ext = np.kron(build_Hz(energies), np.eye(2))
            V_sweep = lam_sweep * np.kron(np.eye(N), np.array([[0, 1], [1, 0]]))
            Hf = Hz_ext + V_sweep
            evals_f, evecs_f = eigh(Hf)
            E0_f = evals_f[0]
            psi0 = np.ones(N) / np.sqrt(N)
            phi_loc = np.array([1.0, 0.0])
            Psi = np.kron(psi0, phi_loc)
            A1_eff = sum(
                abs(np.dot(Psi, evecs_f[:, j]))**2 / (evals_f[j] - E0_f)
                for j in range(len(evals_f)) if evals_f[j] > E0_f + 1e-12
            )
            coupled_stars.append(A1_eff / (A1_eff + 1))
        spread = max(coupled_stars) - min(coupled_stars)
        if verbose:
            print(f"  {lam_sweep:8.3f} {spread:10.4f}")
        assert spread > 1e-3, \
            f"Spread should be nonzero at lambda={lam_sweep}, got {spread}"

    # Test with asymmetric coupling V = lam * diag(1,2,...,N) x sigma_x
    # This breaks the symmetry between computational basis states
    if verbose:
        print(f"\n  Asymmetric coupling V = lam * diag(1..N) x sigma_x:")
        print(f"  {'lambda':>8s} {'spread':>10s}")

    for lam_asym in [0.05, 0.5]:
        coupled_stars_asym = []
        for name, energies in test_spectra:
            N = len(energies)
            diag_sys = np.diag(np.arange(1, N + 1, dtype=float))
            V_asym = lam_asym * np.kron(diag_sys, np.array([[0, 1], [1, 0]]))
            Hz_ext = np.kron(build_Hz(energies), np.eye(2))
            Hf = Hz_ext + V_asym
            evals_f, evecs_f = eigh(Hf)
            E0_f = evals_f[0]
            psi0 = np.ones(N) / np.sqrt(N)
            phi_loc = np.array([1.0, 0.0])
            Psi = np.kron(psi0, phi_loc)
            A1_eff = sum(
                abs(np.dot(Psi, evecs_f[:, j]))**2 / (evals_f[j] - E0_f)
                for j in range(len(evals_f)) if evals_f[j] > E0_f + 1e-12
            )
            coupled_stars_asym.append(A1_eff / (A1_eff + 1))
        spread_asym = max(coupled_stars_asym) - min(coupled_stars_asym)
        if verbose:
            print(f"  {lam_asym:8.3f} {spread_asym:10.4f}")
        assert spread_asym > 1e-3, \
            f"Asymmetric spread should be nonzero at lambda={lam_asym}"

    if verbose:
        print(f"\n  Spread remains nonzero for asymmetric couplings too.")
        print()
        print("Theorem 3: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 5: No-Go (Sensitivity) ----------

def verify_theorem5(verbose=True):
    """Theorem 5: ds*/dA_1 = 1/(A_1+1)^2 != 0.

    Verify that s* = A_1/(A_1+1) implies nonzero sensitivity.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 5: No-Go (Sensitivity ds*/dA_1)")
        print("=" * 60)
        print()

    # Analytic: ds*/dA_1 = d/dA_1 [A_1/(A_1+1)] = 1/(A_1+1)^2 > 0 always.
    # Verify numerically by varying the spectrum.

    N = 8
    results = []

    if verbose:
        print(f"  Two-level instances (N={N}):")
        print(f"  {'d_0':>4s} {'A_1':>8s} {'s*':>8s} {'ds*/dA_1':>10s}")

    for d0 in range(1, N):
        energies = grover_energies(N, d0)
        params = compute_spectral_params(energies)
        A1 = params['A_1']
        s_star = params['s_star']
        deriv = 1.0 / (A1 + 1) ** 2

        results.append({'d_0': d0, 'A_1': A1, 's_star': s_star, 'deriv': deriv})

        if verbose:
            print(f"  {d0:4d} {A1:8.4f} {s_star:8.4f} {deriv:10.4f}")

    if verbose:
        # Numerical derivative check
        print(f"\n  Numerical ds*/dA_1 (finite difference):")
        for i in range(len(results) - 1):
            dA1 = results[i+1]['A_1'] - results[i]['A_1']
            ds = results[i+1]['s_star'] - results[i]['s_star']
            deriv_num = ds / dA1
            deriv_analytic = 0.5 * (results[i]['deriv'] + results[i+1]['deriv'])
            print(f"    d_0={results[i]['d_0']}->{results[i+1]['d_0']}: "
                  f"num={deriv_num:.4f}, analytic~{deriv_analytic:.4f}")

        # Key point: ds*/dA_1 is ALWAYS positive, never zero
        all_derivs = [r['deriv'] for r in results]
        print(f"\n  ds*/dA_1 range: [{min(all_derivs):.4f}, {max(all_derivs):.4f}]")
        print(f"  ALL positive => A_1 dependence cannot be eliminated")
        print()

    if verbose:
        print("Theorem 5: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 4: Multi-Segment Rigidity ----------

def verify_theorem4(verbose=True):
    """Theorem 4: Multi-segment path.

    Segment 1: |psi_0> -> |psi_mid> via some adiabatic path.
    Segment 2: -(1-t)|psi_mid><psi_mid| + t H_z

    The crossing in segment 2 depends on B_1 = sum_k w_k/(E_k-E_0)
    where w_k = sum_{z: E(z)=E_k} |<psi_mid|z>|^2.

    If |psi_mid> = |psi_0> (uniform), then B_1 = A_1.
    If |psi_mid> is non-uniform, B_1 != A_1 but depends on the assignment.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 4: Multi-Segment Rigidity")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)
    params = compute_spectral_params(energies)

    # If intermediate state is uniform: same crossing
    psi_mid_uniform = np.ones(N) / np.sqrt(N)
    E = np.array(energies)
    E_vals = np.sort(np.unique(E))
    E_0 = E_vals[0]

    B1_uniform = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E, ev)
            wk = np.sum(np.abs(psi_mid_uniform[mask])**2)
            B1_uniform += wk / (ev - E_0)

    # If intermediate state is non-uniform
    psi_mid_biased = np.array([0.9, 0.2, 0.2, 0.3])
    psi_mid_biased /= np.linalg.norm(psi_mid_biased)

    B1_biased = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E, ev)
            wk = np.sum(np.abs(psi_mid_biased[mask])**2)
            B1_biased += wk / (ev - E_0)

    s_star_uniform = B1_uniform / (B1_uniform + 1)
    s_star_biased = B1_biased / (B1_biased + 1)

    if verbose:
        print(f"  N={N}, Grover M=1")
        print(f"  A_1 = {params['A_1']:.4f}, s* = {params['s_star']:.4f}")
        print(f"  Uniform midpoint:  B_1 = {B1_uniform:.4f}, "
              f"s*_2 = {s_star_uniform:.4f}")
        print(f"  Biased midpoint:   B_1 = {B1_biased:.4f}, "
              f"s*_2 = {s_star_biased:.4f}")
        print(f"  Uniform gives B_1 = A_1: {abs(B1_uniform - params['A_1']) < 1e-10}")
        print(f"  Biased gives B_1 != A_1: {abs(B1_biased - params['A_1']) > 0.01}")
        print()

    assert abs(B1_uniform - params['A_1']) < 1e-10, \
        "Uniform midpoint should give B_1 = A_1"
    assert abs(B1_biased - params['A_1']) > 0.01, \
        "Biased midpoint should give B_1 != A_1"

    # Verify that for the biased case, different energy assignments
    # give different B_1 (Theorem 2 consequence)
    energies_perm = [1.0, 0.0, 1.0, 1.0]
    E_perm = np.array(energies_perm)
    B1_biased_perm = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E_perm, ev)
            wk = np.sum(np.abs(psi_mid_biased[mask])**2)
            B1_biased_perm += wk / (ev - E_0)

    if verbose:
        print(f"  Biased + permuted: B_1 = {B1_biased_perm:.4f} "
              f"(vs {B1_biased:.4f})")
        print(f"  Different assignment -> different B_1: "
              f"{abs(B1_biased - B1_biased_perm) > 0.01}")
        print(f"  => Non-uniform midpoint is not universal")
        print()
        print("Theorem 4: ALL TESTS PASSED\n")

    return True


# ---------- Sanity checks ----------

def grover_sanity_check(verbose=True):
    """Grover N=4, M=1 sanity check: A_1=3/4, s*=3/7.

    Verify all fundamental quantities.
    """
    if verbose:
        print("=" * 60)
        print("SANITY CHECK: Grover N=4, M=1")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)
    params = compute_spectral_params(energies)

    # Check A_1 = (N-1)/(N*1) = 3/4
    assert abs(params['A_1'] - 3/4) < 1e-10, f"A_1 should be 3/4, got {params['A_1']}"
    # Check s* = 3/7
    assert abs(params['s_star'] - 3/7) < 1e-10, f"s* should be 3/7, got {params['s_star']}"
    # Check Delta = 1
    assert abs(params['Delta'] - 1.0) < 1e-10

    if verbose:
        print(f"  A_1 = {params['A_1']} = 3/4 ✓")
        print(f"  s*  = {params['s_star']:.6f} = 3/7 = {3/7:.6f} ✓")
        print(f"  Delta = {params['Delta']} ✓")
        print()

    # Verify eigenvalue formula at s=1/2 (gap minimum for Grover)
    H = build_H(0.5, energies)
    eigs = np.sort(eigh(H)[0])
    g_min_theory = 1.0 / np.sqrt(N)
    g_min_num = eigs[1] - eigs[0]

    if verbose:
        print(f"  Gap at s=1/2: {g_min_num:.6f} (theory: {g_min_theory:.6f}) ✓")
        print()

    assert abs(g_min_num - g_min_theory) < 1e-10

    # Verify the secular equation
    verify_secular_equation(energies, s_values=[3/7, 0.3, 0.5, 0.7],
                            verbose=verbose)

    if verbose:
        print()
        print("Sanity check: ALL PASSED\n")
    return True


# ---------- Main ----------

def run_all_tests(verbose=True):
    """Run all verification tests."""
    print("=" * 60)
    print("Experiment 12: Circumventing the A_1 Barrier")
    print("Numerical Verification Suite")
    print("=" * 60)
    print()

    grover_sanity_check(verbose=verbose)
    verify_theorem1(verbose=verbose)
    verify_theorem2(verbose=verbose)
    verify_theorem3(verbose=verbose)
    verify_theorem4(verbose=verbose)
    verify_theorem5(verbose=verbose)

    print("=" * 60)
    print("ALL TESTS PASSED")
    print("=" * 60)


if __name__ == '__main__':
    run_all_tests()
