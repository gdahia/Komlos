/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib

/-!
# The one-dimensional tent weight

`Komlos.tent M j = max (M - |j|) 0` is the discrete tent of half-width `M` on `ℤ`. Its square
is (up to normalisation) the one-dimensional marginal of the near-invariant distribution used
in the proof of the Komlós conjecture.

The two facts we need are an exact evaluation of `∑ j, tent M j ^ 2` and the *energy bound*
`∑ j, (tent M j - tent M (j - m)) ^ 2 ≤ 2 * M * m ^ 2`, which is the discrete counterpart of
the estimate obtained in the source paper from the fundamental theorem of calculus and the
Cauchy–Schwarz inequality.
-/

@[expose] public section

namespace Komlos

open Finset

/-- The discrete tent function of half-width `M`. -/
noncomputable def tent (M : ℕ) (j : ℤ) : ℝ := max ((M : ℝ) - |(j : ℝ)|) 0

lemma tent_nonneg (M : ℕ) (j : ℤ) : 0 ≤ tent M j := le_max_right _ _

lemma tent_neg (M : ℕ) (j : ℤ) : tent M (-j) = tent M j := by
  rw [tent, tent]
  push_cast
  rw [abs_neg]

lemma tent_eq_zero {M : ℕ} {j : ℤ} (h : (M : ℤ) ≤ |j|) : tent M j = 0 := by
  rw [tent, max_eq_right]
  have : ((M : ℤ) : ℝ) ≤ ((|j| : ℤ) : ℝ) := Int.cast_le.2 h
  push_cast at this
  linarith

lemma tent_of_abs_le {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) : tent M j = (M : ℝ) - |(j : ℝ)| := by
  rw [tent, max_eq_left]
  have : ((|j| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := Int.cast_le.2 h
  push_cast at this
  linarith

/-- The tent function is `1`-Lipschitz. -/
lemma abs_tent_sub_le (M : ℕ) (j k : ℤ) : |tent M j - tent M k| ≤ |(j : ℝ) - (k : ℝ)| := by
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [(by ring : (M : ℝ) - |(j : ℝ)| - ((M : ℝ) - |(k : ℝ)|) = |(k : ℝ)| - |(j : ℝ)|)]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq (abs_sub_comm _ _))

lemma sum_range_sq (n : ℕ) : (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) * 6
    = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

@[simp] lemma tent_zero (M : ℕ) : tent M 0 = M := by
  rw [tent]
  norm_num

/-- Two finite sums of a function agree whenever both index sets contain its support. -/
lemma sum_eq_of_support {ι : Type*} {g : ι → ℝ} {s t : Finset ι}
    (hs : ∀ j, g j ≠ 0 → j ∈ s) (ht : ∀ j, g j ≠ 0 → j ∈ t) : ∑ j ∈ s, g j = ∑ j ∈ t, g j := by
  classical
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := t)) (fun x _ hx => by grind),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun x _ hx => by grind)]

lemma sum_Icc_neg {g : ℤ → ℝ} (hg : ∀ j, g (-j) = g j) (M : ℕ) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) M, g j = g 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℤ) M, g j := by
  have hrefl : ∑ j ∈ Finset.Icc (-(M : ℤ)) 0, g j = ∑ j ∈ Finset.Icc (0 : ℤ) M, g j := by
    refine Finset.sum_nbij' (fun j => -j) (fun j => -j) (fun a ha => ?_) (fun a ha => ?_)
      (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun a _ => (hg a).symm)
    · rw [Finset.mem_Icc] at ha ⊢
      grind
    · rw [Finset.mem_Icc] at ha ⊢
      grind
  have hins : Finset.Icc (0 : ℤ) M = insert (0 : ℤ) (Finset.Icc (1 : ℤ) (M : ℤ)) := by
    ext j
    rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
    grind
  have hsplit : Finset.Icc (-(M : ℤ)) M = Finset.Icc (-(M : ℤ)) 0 ∪ Finset.Icc 1 M := by
    ext j
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    grind
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ)) 0) (Finset.Icc 1 M) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    grind
  have h0 : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) M := by
    rw [Finset.mem_Icc]
    grind
  rw [hsplit, Finset.sum_union hdisj, hrefl, hins, Finset.sum_insert h0]
  ring

lemma sum_Icc_reflect (M : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) M, h ((M : ℤ) - j).toNat = ∑ i ∈ Finset.range M, h i := by
  refine Finset.sum_nbij' (fun j => ((M : ℤ) - j).toNat) (fun i => (M : ℤ) - i)
    (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a _ => rfl)
  · rw [Finset.mem_Icc] at ha
    rw [Finset.mem_range]
    grind
  · rw [Finset.mem_range] at ha
    rw [Finset.mem_Icc]
    grind
  · rw [Finset.mem_Icc] at ha
    grind
  · rw [Finset.mem_range] at ha
    grind

/-- The exact value of the squared `L²` norm of the tent: `∑ j, tent M j ^ 2 = M (2M² + 1)/3`. -/
lemma sum_tent_sq (M : ℕ) :
    (∑ j ∈ Finset.Icc (-(M : ℤ)) M, tent M j ^ 2) * 3 = (M : ℝ) * (2 * (M : ℝ) ^ 2 + 1) := by
  have heven : ∀ j : ℤ, tent M (-j) ^ 2 = tent M j ^ 2 := fun j => by rw [tent_neg]
  have hval : ∀ j ∈ Finset.Icc (1 : ℤ) M,
      tent M j ^ 2 = ((((M : ℤ) - j).toNat : ℕ) : ℝ) ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hcast : ((((M : ℤ) - j).toNat : ℕ) : ℝ) = (M : ℝ) - (j : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by grind : (0 : ℤ) ≤ (M : ℤ) - j)]
      push_cast
      ring
    rw [tent_of_abs_le (by grind), abs_of_nonneg (by exact_mod_cast (by grind : (0 : ℤ) ≤ j)),
      hcast]
  rw [sum_Icc_neg heven M, Finset.sum_congr rfl hval,
    sum_Icc_reflect M (fun i => ((i : ℕ) : ℝ) ^ 2), tent_zero]
  nlinarith [sum_range_sq M]

/-- The one-step difference of the tent. -/
noncomputable def step (M : ℕ) (j : ℤ) : ℝ := tent M j - tent M (j - 1)

lemma abs_step_le_one (M : ℕ) (j : ℤ) : |step M j| ≤ 1 := by
  rw [step]
  refine (abs_tent_sub_le M j (j - 1)).trans ?_
  push_cast
  norm_num

lemma step_eq_zero {M : ℕ} {j : ℤ} (h : j ∉ Finset.Icc (1 - (M : ℤ)) M) : step M j = 0 := by
  rw [Finset.mem_Icc, not_and_or] at h
  have h1 : (M : ℤ) ≤ |j| := by
    rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind
  have h2 : (M : ℤ) ≤ |j - 1| := by
    rcases abs_cases (j - 1) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind
  rw [step, tent_eq_zero h1, tent_eq_zero h2, sub_zero]

lemma sum_step_sq_le (M : ℕ) {s : Finset ℤ} (hs : ∀ j, step M j ≠ 0 → j ∈ s) :
    ∑ j ∈ s, step M j ^ 2 ≤ 2 * M := by
  have hsupp : ∀ j : ℤ, step M j ^ 2 ≠ 0 → j ∈ Finset.Icc (1 - (M : ℤ)) M := by
    intro j hj
    by_contra hcon
    rw [step_eq_zero hcon] at hj
    exact hj (by ring)
  rw [sum_eq_of_support (fun j hj => hs j (by grind)) hsupp]
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun j _ => ?_)).trans ?_
  · nlinarith [abs_step_le_one M j, abs_nonneg (step M j), sq_abs (step M j)]
  · have hcard : (Finset.Icc (1 - (M : ℤ)) M).card = 2 * M := by
      rw [Int.card_Icc]
      omega
    rw [hcard, nsmul_eq_mul, mul_one]
    push_cast
    norm_num

lemma sum_shift_index (g : ℤ → ℝ) (i a b : ℤ) :
    ∑ j ∈ Finset.Icc (a - i) (b - i), g j = ∑ j ∈ Finset.Icc a b, g (j - i) := by
  rw [sub_eq_add_neg a i, sub_eq_add_neg b i, ← Finset.map_add_right_Icc, Finset.sum_map]
  congr

lemma shift_diff_eq_zero {M m : ℕ} {j : ℤ} (h : j ∉ Finset.Icc (-((M : ℤ) + m)) ((M : ℤ) + m)) :
    tent M j - tent M (j - (m : ℤ)) = 0 := by
  rw [Finset.mem_Icc, not_and_or] at h
  have h1 : (M : ℤ) ≤ |j| := by
    rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind
  have h2 : (M : ℤ) ≤ |j - (m : ℤ)| := by
    rcases abs_cases (j - (m : ℤ)) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind
  rw [tent_eq_zero h1, tent_eq_zero h2, sub_zero]

/-- **Energy bound**, natural-number shifts: the discrete analogue of the estimate obtained in
the source paper from the fundamental theorem of calculus and Cauchy–Schwarz. -/
lemma sum_tent_shift_sq_le_nat (M m : ℕ) {s : Finset ℤ}
    (hs : ∀ j, tent M j - tent M (j - (m : ℤ)) ≠ 0 → j ∈ s) :
    ∑ j ∈ s, (tent M j - tent M (j - (m : ℤ))) ^ 2 ≤ 2 * M * (m : ℝ) ^ 2 := by
  have hsupp : ∀ j : ℤ, (tent M j - tent M (j - (m : ℤ))) ^ 2 ≠ 0 →
      j ∈ Finset.Icc (-((M : ℤ) + m)) ((M : ℤ) + m) := by
    intro j hj
    by_contra hcon
    rw [shift_diff_eq_zero hcon] at hj
    exact hj (by ring)
  have htel : ∀ j : ℤ, tent M j - tent M (j - (m : ℤ)) = ∑ i ∈ Finset.range m, step M (j - i) := by
    intro j
    have htl := Finset.sum_range_sub' (fun i => tent M (j - (i : ℤ))) m
    simp only [Nat.cast_zero, sub_zero] at htl
    rw [← htl]
    congr with i
    rw [step]
    congr 2
    push_cast
    ring
  have hptwise : ∀ j : ℤ, (tent M j - tent M (j - (m : ℤ))) ^ 2
      ≤ (m : ℝ) * ∑ i ∈ Finset.range m, step M (j - i) ^ 2 := by
    intro j
    rw [htel j]
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ => (1 : ℝ))
      (fun i => step M (j - i))
  rw [sum_eq_of_support (fun j hj => hs j (by grind)) hsupp]
  refine (Finset.sum_le_sum (fun j _ => hptwise j)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range m,
      ∑ j ∈ Finset.Icc (-((M : ℤ) + m)) ((M : ℤ) + m), step M (j - i) ^ 2 ≤ 2 * M := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← sum_shift_index (fun j => step M j ^ 2) i]
    refine sum_step_sq_le M (fun j hj => ?_)
    rw [Finset.mem_Icc]
    have := step_eq_zero (M := M) (j := j)
    grind
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by positivity)).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  norm_num

/-- **Energy bound** for arbitrary integer shifts:
`∑ j, (tent M j - tent M (j - m)) ^ 2 ≤ 2 M m²`. -/
lemma sum_tent_shift_sq_le (M : ℕ) (m : ℤ) {s : Finset ℤ}
    (hs : ∀ j, tent M j - tent M (j - m) ≠ 0 → j ∈ s) :
    ∑ j ∈ s, (tent M j - tent M (j - m)) ^ 2 ≤ 2 * M * (m : ℝ) ^ 2 := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact sum_tent_shift_sq_le_nat M k hs
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt (neg_pos.2 hm))
    have hkm : m = -(k : ℤ) := by omega
    subst hkm
    have hs' : ∀ j : ℤ, tent M j - tent M (j - (k : ℤ)) ≠ 0 →
        j ∈ s.map (addRightEmbedding (k : ℤ)) := by
      intro j hj
      rw [Finset.mem_map]
      refine ⟨j - (k : ℤ), hs (j - (k : ℤ)) ?_, ?_⟩
      · rw [sub_neg_eq_add, sub_add_cancel]
        intro hzero
        exact hj (by linarith [sub_eq_zero.1 hzero])
      · rw [addRightEmbedding_apply, sub_add_cancel]
    have key := sum_tent_shift_sq_le_nat M k hs'
    rw [Finset.sum_map] at key
    have heq : ∀ j ∈ s, (tent M j - tent M (j - -(k : ℤ))) ^ 2
        = (tent M (addRightEmbedding (k : ℤ) j)
            - tent M (addRightEmbedding (k : ℤ) j - (k : ℤ))) ^ 2 := by
      intro j _
      rw [addRightEmbedding_apply, add_sub_cancel_right, sub_neg_eq_add]
      ring
    rw [Finset.sum_congr rfl heq]
    refine key.trans (le_of_eq ?_)
    push_cast
    ring

end Komlos
