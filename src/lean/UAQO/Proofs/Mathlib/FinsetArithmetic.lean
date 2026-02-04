/-
  Common Finset lemmas needed across multiple proofs.

  These bridge lemmas connect UAQO definitions to Mathlib's Finset API.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset

namespace UAQO.Proofs.Mathlib

/-- Sum over a disjoint partition equals total. -/
lemma sum_partition_eq_total {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {s : Finset α} {f : α → β} {P : α → Nat}
    (hpart : ∀ a ∈ s, ∃ k, P a = k) :
    Finset.sum s f = Finset.sum (Finset.image P s) (fun k =>
      Finset.sum (Finset.filter (fun a => P a = k) s) f) := by
  rw [← Finset.sum_fiberwise_of_maps_to]
  · rfl
  · intro a ha
    exact Finset.mem_image_of_mem P ha

/-- Cardinality of disjoint union equals sum of cardinalities. -/
lemma card_biUnion_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset β} {f : β → Finset α}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (Finset.biUnion s f).card = Finset.sum s (fun i => (f i).card) := by
  exact Finset.card_biUnion hdisj

/-- Sum splits into filtered parts. -/
lemma sum_filter_add_sum_filter_not {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    Finset.sum s f = Finset.sum (Finset.filter p s) f +
                     Finset.sum (Finset.filter (fun a => ¬p a) s) f := by
  rw [← Finset.sum_union]
  · congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    tauto
  · intro a ha1 ha2
    simp only [Finset.mem_filter] at ha1 ha2
    exact ha1.2 ha2.2

/-- Finset.sum respects equality of functions. -/
lemma sum_congr_fun {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (f g : α → β) (h : ∀ a ∈ s, f a = g a) :
    Finset.sum s f = Finset.sum s g :=
  Finset.sum_congr rfl h

/-- Powers of 2 sum formula. -/
lemma sum_pow_two_eq (n : Nat) :
    Finset.sum (Finset.range n) (fun i => 2^i) = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf
    omega

/-- Fin.sum version of powers of 2. -/
lemma fin_sum_pow_two (n : Nat) (hn : n > 0) :
    Finset.sum Finset.univ (fun i : Fin n => 2^i.val) = 2^n - 1 := by
  have h : Finset.sum Finset.univ (fun i : Fin n => 2^i.val) =
           Finset.sum (Finset.range n) (fun i => 2^i) := by
    rw [← Finset.sum_map]
    congr 1
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, Finset.mem_range, true_and]
    constructor
    · intro ⟨j, hj⟩
      rw [← hj]
      exact j.isLt
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [h, sum_pow_two_eq]

end UAQO.Proofs.Mathlib
