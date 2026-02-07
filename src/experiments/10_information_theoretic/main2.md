# Information-Theoretic Limits: Addendum (Open-Item Resolution)

## Purpose

This addendum resolves the remaining open item from `main.md` using
`proof2.md` while keeping the primary files readable.

## Statement Resolved

After refuting literal Conjecture 5 in `proof.md` (Part IX), the remaining question was:

For fixed instance-independent continuous-time rank-one controls, is there a worst-case
diagonal instance forcing $\Omega(N/\sqrt{d_0})$ runtime?

## Resolution

`proof2.md` proves the worst-case statement under explicit control normalization.

**Theorem 10 (`proof2.md`).**
If $|g(t)|\le 1$ for all $t$ and the algorithm must succeed on the scaled unstructured
family
$$
H_z^{(S,\delta)}=\delta(\mathbb{I}-P_S),\quad |S|=d_0,
$$
then
$$
T=\Omega\!\left(\frac{\sqrt{N/d_0}}{\delta}\right).
$$
Choosing $\delta=N^{-1/2}$ yields
$$
T=\Omega\!\left(\frac{N}{\sqrt{d_0}}\right).
$$

## Interpretation

The apparent contradiction in Part IX is now resolved cleanly:

1. Literal Conjecture 5 is false without normalization (fast family-level protocol exists).
2. The normalized worst-case reformulation is true.

The normalization step is essential. Without amplitude/action control, physical-time
lower bounds are ill-posed by simple time-rescaling (Proposition 11 in `proof2.md`).

## Integration Note

Use `main.md` for the global narrative and status table.
Use `proof.md` for core Parts I-X.
Use `main2.md` / `proof2.md` for this open-item completion layer.
