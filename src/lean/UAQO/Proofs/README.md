# UAQO Proofs Directory

Auxiliary proof files that delegate to theorems in main UAQO files.

See the main [README.md](../../README.md) for:
- Complete axiom status and tracking
- Eliminated axioms list
- Formulation fixes applied
- Future work priorities

## Directory Structure

```
Proofs/
    Foundations/           Variational principle (delegates to SpectralTheory.lean)
    Spectral/              Sherman-Morrison (delegates to GapBounds.lean)
    Adiabatic/             Schedule properties
    Complexity/            SAT semantics, beta-modified Hamiltonian
    Mathlib/               Bridge lemmas
```

All proofs in this directory reference theorems already proved in the main files.
