# Main Story

AQO is powerful enough to match the best quantum algorithm for unstructured optimization, but the mechanism that gets it there pays a cost in spectral information that the circuit model does not pay.

## Why AQC

It is a genuinely different model of quantum computation: continuous Hamiltonian evolution, not discrete gates. Polynomially equivalent to circuits, so universal in principle. But the equivalence is constructive in the wrong way: it simulates circuits gate-by-gate, producing a protocol that has nothing to do with the natural AQO formulation. So AQC's capabilities have to be understood on its own terms.

## Why AQO

AQO is the original purpose of the framework: encode a cost function as a diagonal Hamiltonian, interpolate from an easy ground state, let the gap control the runtime. It is the most physically natural application and the least understood. The runtime depends on the minimum spectral gap along the entire interpolation, which is notoriously hard to bound.

## What We Show

Three things, in sequence:

1. AQO matches the Grover lower bound for all diagonal Hamiltonians with polynomially bounded spectral data. The quantum speed limit is achievable.

2. Achieving it requires knowing A_1, a spectral parameter that locates the avoided crossing, to exponential precision. Computing A_1 is #P-hard. Harder than the optimization problem itself.

3. The circuit model (Durr-Hoyer) achieves the same speedup with zero spectral knowledge. The discrepancy is structural: slow interpolation through a gap minimum creates an information requirement that the problem itself does not have.

## Why It Matters

The thesis maps out both the power and the price of AQO's physical mechanism. AQO reaches the quantum speed limit, but its mechanism (adiabatic tracking through an avoided crossing) demands knowledge that is computationally harder to obtain than the answer it is trying to find. That is the information gap. It is not a bug in the schedule or a failure of analysis. It is a structural feature of the framework.
