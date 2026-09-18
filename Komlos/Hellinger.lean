/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.ShiftDistance

/-!
# Bounding total variation by the `L²` distance of square roots

The Cauchy–Schwarz inequality bounds the total variation distance of two probability
distributions by the Euclidean distance between their pointwise square roots. Writing the
distributions as `p ^ 2` and `q ^ 2` keeps square roots out of the statement, which is
convenient because the distributions used in the proof of the Komlós conjecture are built as
squares of products of tent functions.
-/

@[expose] public section

namespace Komlos

open Finsupp Finset

variable {E : Type*}

/-- Cauchy–Schwarz: the total variation distance between `p ^ 2` and `q ^ 2` is at most the
`L²` distance between `p` and `q`. -/
lemma tvDist_sq_le {P Q : E →₀ ℝ} (hP : IsDist P) (hQ : IsDist Q) {s : Finset E}
    (hPs : P.support ⊆ s) (hQs : Q.support ⊆ s) (p q : E → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hP2 : ∀ x ∈ s, P x = p x ^ 2) (hQ2 : ∀ x ∈ s, Q x = q x ^ 2) :
    tvDist P Q ^ 2 ≤ ∑ x ∈ s, (p x - q x) ^ 2 := by
  have habs : ∀ x ∈ s, |P x - Q x| = |p x - q x| * (p x + q x) := by
    intro x hx
    rw [hP2 x hx, hQ2 x hx, sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hp x) (hq x)),
      mul_comm]
  have hbound : ∑ x ∈ s, (p x + q x) ^ 2 ≤ 4 := by
    have hterm : ∀ x ∈ s, (p x + q x) ^ 2 ≤ 2 * (P x + Q x) := by
      intro x hx
      rw [hP2 x hx, hQ2 x hx]
      nlinarith [sq_nonneg (p x - q x)]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← mass_eq_sum hPs, ← mass_eq_sum hQs,
      hP.mass_eq, hQ.mass_eq]
    norm_num
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => |p x - q x|) (fun x => p x + q x)
  have habs2 : ∑ x ∈ s, |p x - q x| ^ 2 = ∑ x ∈ s, (p x - q x) ^ 2 := by
    congr with x
    rw [sq_abs]
  rw [habs2] at hcs
  have hnn : 0 ≤ ∑ x ∈ s, (p x - q x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  rw [tvDist_eq_sum hPs hQs, Finset.sum_congr rfl habs]
  nlinarith [hcs, hbound, hnn, Finset.sum_nonneg (fun x (_ : x ∈ s) =>
    mul_nonneg (abs_nonneg (p x - q x)) (add_nonneg (hp x) (hq x)))]

/-- Weierstrass' product inequality. -/
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hrest : 1 - ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 - a i) :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hsum : 0 ≤ ∑ i ∈ t, a i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have haj : a j ≤ 1 := h1 j (Finset.mem_insert_self j t)
    nlinarith [h0 j (Finset.mem_insert_self j t)]

end Komlos
