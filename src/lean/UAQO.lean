/-
  Unstructured Adiabatic Quantum Optimization: Optimality with Limitations

  This is a formal verification in Lean 4 of the paper:
  "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations"
  by Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland

  The formalization covers:
  1. Foundations: Quantum mechanics basics (Hilbert spaces, operators, spectral theory)
  2. Adiabatic quantum computation framework
  3. Spectral gap analysis of adiabatic Hamiltonians
  4. The adiabatic theorem and running time analysis
  5. Complexity-theoretic hardness results (NP-hard and #P-hard)
-/

import UAQO.Foundations.Basic
import UAQO.Foundations.HilbertSpace
import UAQO.Foundations.Operators
import UAQO.Foundations.SpectralTheory
import UAQO.Foundations.Qubit

import UAQO.Spectral.DiagonalHamiltonian
import UAQO.Spectral.SpectralParameters
import UAQO.Spectral.GapBounds

import UAQO.Adiabatic.Hamiltonian
import UAQO.Adiabatic.Schedule
import UAQO.Adiabatic.Theorem
import UAQO.Adiabatic.RunningTime

import UAQO.Complexity.Basic
import UAQO.Complexity.NP
import UAQO.Complexity.SharpP
import UAQO.Complexity.Hardness

import UAQO.Test.Verify
