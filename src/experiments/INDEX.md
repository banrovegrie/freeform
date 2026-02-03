# Experiments Index

Summary of all research explorations conducted, with validation status.


## Validated Results

### Gap Formula for H(r)
**Status**: VALIDATED

For H(r) = -|psi_0><psi_0| + r*H_z, the minimum gap occurs at r = A_1 with value:
```
g_min = 2 * A_1 * sqrt(d_0 / (A_2 * N))
```

Numerical validation: <2% error for n = 8, 10, 12 qubits.

**Files**: `refined_resonance_analysis.py`, `find_resonance_empirical.py`


### Imprecision-Fidelity Tradeoff
**Status**: VALIDATED

| A_1 Error | Fidelity Loss |
|-----------|---------------|
| 1%        | <1%           |
| 5%        | ~4%           |
| 10%       | ~8%           |
| 50%       | ~37%          |

Uniform schedule (no A_1 needed) matches local schedule with ~20% error.

**File**: `local_schedule_simulation.py`


## Failed Approaches

### Loschmidt Echo Calibration
**Status**: FAILED

Two-level approximation insufficient. Multi-level interference destroys signal.

**Files**: `validate_resonance.py`, `loschmidt_dynamics.py`


### QPE-Based Calibration
**Status**: NEGATIVE RESULT

Complexity O(n * N/d_0) is worse than uncalibrated AQO.

**File**: `qpe_calibration.md`


## File Manifest

| File | Description | Status |
|------|-------------|--------|
| `research_proposals.md` | 10 research directions | Reference |
| `error_analysis_imprecise_A1.md` | Theoretical analysis | Partially valid |
| `numerical_framework.md` | Computational plans | Reference |
| `non_adiabatic_oscillation.md` | Oscillation algorithm | Needs revision |
| `qaoa_connection.md` | QAOA relationship | Exploratory |
| `quantum_calibration_theorem.md` | Original theorem | Superseded |
| `loschmidt_echo_proofs.md` | Mathematical analysis | Partially valid |
| `qpe_calibration.md` | QPE approach | Negative result |
| `RIGOROUS_ASSESSMENT.md` | Honest status | Current |
| `FINAL_SYNTHESIS.md` | Publishable summary | Current |
| `refined_resonance_analysis.py` | Gap validation | Validated |
| `find_resonance_empirical.py` | Resonance study | Validated |
| `loschmidt_dynamics.py` | Echo analysis | Shows failure |
| `local_schedule_simulation.py` | Imprecision test | Validated |
| `validate_resonance.py` | Initial test | Superseded |
| `imprecise_A1_simulation.py` | Early version | Superseded |
| `quantum_calibration_simulation.py` | Full version | Needs scipy |


## Open Questions

1. Is there ANY quantum protocol to estimate A_1 efficiently?
2. What is complexity of A_1 approximation at intermediate precisions?
3. Are there structured problem classes where A_1 is tractable?


## Potential Publications

**Option A**: Negative result on quantum calibration robustness

**Option B**: Practical AQO without exact spectral knowledge (imprecision tradeoff)

See `FINAL_SYNTHESIS.md` for detailed paper outlines.
