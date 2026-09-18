/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.NearInvariant
public import Komlos.SignedSums

/-!
# The Komlós conjecture for grid vectors

Combining Lemma 1.4 (`Komlos.exists_signs`) with Lemma 1.5 (`Komlos.exists_nearInvariant`)
proves the Komlós conjecture, with constant `36`, for vectors lying on a grid `N⁻¹ • ℤ ^ d`.
-/

@[expose] public section

namespace Komlos

open Finset Finsupp

/-- A coordinate box is convex. -/
lemma convex_box (d : ℕ) (c : ℝ) : Convex ℝ {x : Fin d → ℝ | ∀ k, |x k| ≤ c} := by
  intro x hx y hy a b ha hb hab k
  simp only [Set.mem_ofPred_eq] at hx hy
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum : a * c + b * c = c := by
    rw [← add_mul, hab, one_mul]
  linarith [mul_nonneg ha (sub_nonneg.2 (hx k)), mul_nonneg hb (sub_nonneg.2 (hy k))]

/-- **The Komlós conjecture for grid vectors**: a matrix whose columns lie on the grid
`N⁻¹ • ℤ ^ d` and have Euclidean norm at most `1` has discrepancy at most `36`. -/
theorem discrepancy_le_of_grid {d n N : ℕ} (hN : 0 < N) (g : Fin n → Fin d → ℤ)
    (hg : ∀ i, ∑ k, ((g i k : ℝ) / N) ^ 2 ≤ 1) :
    discrepancy (Matrix.of fun (k : Fin d) (i : Fin n) => (g i k : ℝ) / N) ≤ 36 := by
  obtain ⟨P, hP, hmean, hbox, hshift⟩ := exists_nearInvariant (d := d) hN
  obtain ⟨ε, hε, hmem⟩ := exists_isColouring_mean_add_sum_mem_convexHull n P hP
    (fun i => (6 : ℝ)⁻¹ • fun k => (g i k : ℝ) / N)
    (fun i => by
      rw [smul_smul, (by norm_num : (6 : ℝ) * 6⁻¹ = 1), one_smul]
      exact hshift (g i) (hg i))
  refine discrepancy_le_iff.2 ⟨ε, hε, (colouringDiscrepancy_le_iff (by norm_num)).2 fun k => ?_⟩
  have hsub : (P.support : Set (Fin d → ℝ)) ⊆ {x : Fin d → ℝ | ∀ k, |x k| ≤ 6} :=
    fun x hx => hbox x hx
  have hin := convexHull_min hsub (convex_box d 6) hmem
  rw [hmean, zero_add] at hin
  have hval : (∑ i, ε i • (6 : ℝ)⁻¹ • fun k => (g i k : ℝ) / N) k
      = (6 : ℝ)⁻¹ * ∑ i, Matrix.of (fun (k : Fin d) (i : Fin n) => (g i k : ℝ) / N) k i * ε i := by
    rw [Finset.sum_apply, Finset.mul_sum]
    congr with i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.of_apply]
    ring
  have hk := hin k
  rw [hval, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (6 : ℝ)⁻¹)] at hk
  linarith

end Komlos
