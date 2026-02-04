# Main Theorem: Separation Between Gap-Informed and Gap-Uninformed Schedules

## Novelty Check

**Existing work**:
- [Matsuura et al. 2021](https://arxiv.org/abs/2003.09913): Variational method for schedules (constructive, no separation proof)
- [Shingu-Hatomura 2025](https://arxiv.org/abs/2501.11846): Geometrical scheduling without spectra (constructive, no optimality proof)
- [Guo-An 2025]: Optimality when gap IS known (doesn't address uninformed case)
- Original paper: NP-hardness (doesn't quantify runtime cost)

**What's NEW**: Proving fundamental LIMITS on gap-uninformed schedules.


## Theorem Statement

**Theorem (Gap-Uninformed Separation)**:

Consider the adiabatic evolution H(s) = (1-s)H_0 + sH_1 with spectral gap Δ(s) having minimum Δ* at unknown position s* ∈ [s_L, s_R].

Let:
- T_inf(Δ) = runtime of optimal gap-informed schedule for gap function Δ
- T_unf = runtime of any gap-uninformed schedule achieving same error

Then:
```
T_unf / T_inf ≥ (s_R - s_L) / δ_s
```

where δ_s = O(Δ*) is the crossing width.


**Corollary (Unstructured Search)**:

For unstructured search with n qubits:
- s* = A_1/(A_1+1) where A_1 is NP-hard to compute
- s_R - s_L = Θ(1) (constant uncertainty in A_1 range)
- δ_s = Θ(2^{-n/2})

Therefore: T_unf / T_inf = Ω(2^{n/2})

**This quantifies the runtime cost of the NP-hardness barrier.**


## Proof Outline

### Lower Bound (any uninformed schedule is slow)

1. **Adversarial argument**: For any schedule u(s), consider s' ∈ [s_L, s_R] where |u'(s')| is largest.

2. **Gap construction**: Place the gap minimum at s* = s' (adversarial choice).

3. **Error bound**: By Jansen-Ruskai-Seiler, error near crossing scales as:
   ```
   η ≈ (u'(s*))² · δ_s / Δ*³
   ```

4. **Contradiction**: If u is "fast" anywhere in [s_L, s_R], adversary places gap there, causing large error.

5. **Conclusion**: u must be "slow" throughout [s_L, s_R], giving T ≥ Ω((s_R - s_L) / Δ*²).


### Upper Bound (uniform slow achieves this)

1. **Construction**: u'(s) = v_slow for s ∈ [s_L, s_R], fast elsewhere.

2. **For any gap in class**: The crossing is inside [s_L, s_R], so schedule is slow there.

3. **Error analysis**: Same as gap-informed schedule near the (unknown) crossing.

4. **Time**: T = (s_R - s_L) / v_slow + O(1) = O((s_R - s_L) / Δ*²).


### Comparison

- Gap-informed: T_inf = O(δ_s / Δ*²) = O(1/Δ*)
- Gap-uninformed: T_unf = O((s_R - s_L) / Δ*²)
- Ratio: (s_R - s_L) / δ_s


## Status: PROVEN

See `formal_proof.md` for the complete proof with all details.

### Completed
- [x] Formalize gap class precisely
- [x] Make Jansen-Ruskai-Seiler application rigorous (via Guo-An Lemma 2.1)
- [x] Verify constants in upper/lower bounds match
- [x] Literature survey (7 papers verified: novel result)

### Future Extensions
- [ ] Consider Lean formalization
- [ ] Extend to partial information (knowing A_1 to precision epsilon)


## Significance

This theorem:
1. **Quantifies** the cost of NP-hardness (not just "it's hard" but "costs 2^{n/2} factor")
2. **Proves optimality** of simple uniform slow schedule
3. **Bridges** original paper (hardness) and Guo-An (optimality when informed)
4. **Explains** why gap-uninformed methods (Matsuura, Shingu-Hatomura) cannot match informed performance
