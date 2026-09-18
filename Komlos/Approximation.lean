/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib

/-!
# Approximating real vectors by grid vectors

Truncating each coordinate toward zero approximates a real vector by a vector on the grid
`N⁻¹ • ℤ ^ d` without increasing the absolute value of any coordinate, hence without increasing
the Euclidean norm.
-/

@[expose] public section

namespace Komlos

open Finset

/-- Truncation toward zero on the grid `N⁻¹ • ℤ`. -/
lemma exists_int_approx (x : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℤ, |(m : ℝ) / N| ≤ |x| ∧ |x - (m : ℝ) / N| ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have h0 : (0 : ℝ) ≤ (⌊|x| * N⌋ : ℤ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  have hle : ((⌊|x| * N⌋ : ℤ) : ℝ) ≤ |x| * N := Int.floor_le _
  have hlt : |x| * N < (⌊|x| * N⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  have hdiv : ((⌊|x| * N⌋ : ℤ) : ℝ) / N ≤ |x| := by
    rw [div_le_iff₀ hN']
    exact hle
  rcases le_or_gt 0 x with hx | hx
  · refine ⟨⌊|x| * N⌋, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity), abs_of_nonneg hx] at *
      exact hdiv
    · rw [abs_of_nonneg hx] at *
      rw [abs_of_nonneg (by linarith), le_div_iff₀ hN', sub_mul, div_mul_cancel₀ _ hN'.ne']
      linarith
  · refine ⟨-⌊|x| * N⌋, ?_, ?_⟩
    · rw [abs_of_neg hx] at *
      rw [Int.cast_neg, neg_div, abs_neg, abs_of_nonneg (by positivity)]
      exact hdiv
    · rw [abs_of_neg hx] at *
      rw [Int.cast_neg, neg_div, sub_neg_eq_add, abs_of_nonpos (by linarith), le_div_iff₀ hN',
        neg_mul, add_mul, div_mul_cancel₀ _ hN'.ne']
      linarith

/-- A real configuration can be approximated coordinatewise by a grid configuration without
increasing any coordinate in absolute value. -/
lemma exists_grid_approx {d n : ℕ} (v : Fin n → Fin d → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (g : Fin n → Fin d → ℤ), 0 < N ∧ (∀ i k, |(g i k : ℝ) / N| ≤ |v i k|) ∧
      ∀ i k, |v i k - (g i k : ℝ) / N| ≤ η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast this
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hinv : 1 / (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hN']
    rw [div_lt_iff₀ hη] at hN
    linarith
  choose g hg1 hg2 using fun (i : Fin n) (k : Fin d) => exists_int_approx (v i k) hNpos
  exact ⟨N, g, hNpos, hg1, fun i k => (hg2 i k).trans hinv⟩

end Komlos
