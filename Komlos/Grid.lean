/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Tent

/-!
# The normalised one-dimensional grid weight

Fix a positive integer `N`. The grid is `N⁻¹ • ℤ` and the cube is `[-6, 6]`, so the grid points
in the cube are indexed by the integers of absolute value at most `gridM N = 6 * N`. The
function `gridF N` is the tent of half-width `gridM N`, normalised so that `∑ j, gridF N j ^ 2`
is `1`; thus `gridF N ^ 2` is a probability distribution on the grid.
-/

@[expose] public section

namespace Komlos

open Finset

/-- Half-width of the grid: the cube `[-6, 6]` with spacing `N⁻¹` has `6 * N` grid points on
each side of the origin. -/
def gridM (N : ℕ) : ℕ := 6 * N

/-- The normalising constant `∑ j, tent (gridM N) j ^ 2`. -/
noncomputable def gridZ (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (-(gridM N : ℤ)) (gridM N), tent (gridM N) j ^ 2

/-- The normalised one-dimensional weight. -/
noncomputable def gridF (N : ℕ) (j : ℤ) : ℝ := tent (gridM N) j / Real.sqrt (gridZ N)

lemma gridZ_mul_three (N : ℕ) :
    gridZ N * 3 = (gridM N : ℝ) * (2 * (gridM N : ℝ) ^ 2 + 1) := sum_tent_sq _

lemma gridZ_pos {N : ℕ} (hN : 0 < N) : 0 < gridZ N := by
  have hM : (0 : ℝ) < (gridM N : ℝ) := by
    rw [gridM]
    positivity
  nlinarith [gridZ_mul_three N]

lemma gridF_nonneg (N : ℕ) (j : ℤ) : 0 ≤ gridF N j :=
  div_nonneg (tent_nonneg _ _) (Real.sqrt_nonneg _)

lemma gridF_eq_zero {N : ℕ} {j : ℤ} (h : (gridM N : ℤ) ≤ |j|) : gridF N j = 0 := by
  rw [gridF, tent_eq_zero h, zero_div]

lemma gridF_ne_zero_mem {N : ℕ} {j : ℤ} (h : gridF N j ≠ 0) :
    j ∈ Finset.Icc (-(gridM N : ℤ)) (gridM N) := by
  rw [Finset.mem_Icc]
  by_contra hcon
  refine h (gridF_eq_zero ?_)
  rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind

lemma sum_gridF_sq {N : ℕ} (hN : 0 < N) {K : Finset ℤ}
    (hK : ∀ j, gridF N j ≠ 0 → j ∈ K) : ∑ j ∈ K, gridF N j ^ 2 = 1 := by
  have hsupp : ∀ j : ℤ, gridF N j ^ 2 ≠ 0 → j ∈ Finset.Icc (-(gridM N : ℤ)) (gridM N) :=
    fun j hj => gridF_ne_zero_mem (by grind)
  rw [sum_eq_of_support (fun j hj => hK j (by grind)) hsupp]
  have hval : ∀ j ∈ Finset.Icc (-(gridM N : ℤ)) (gridM N),
      gridF N j ^ 2 = tent (gridM N) j ^ 2 / gridZ N := by
    intro j _
    rw [gridF, div_pow, Real.sq_sqrt (gridZ_pos hN).le]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_div, ← gridZ, div_self (gridZ_pos hN).ne']

/-- The key one-dimensional estimate: shifting by `m` moves `gridF` by at most `|m| / (N √12)`
in `L²`. -/
lemma sum_gridF_shift_sq_le {N : ℕ} (hN : 0 < N) (m : ℤ) {K : Finset ℤ}
    (hK : ∀ j, gridF N j - gridF N (j - m) ≠ 0 → j ∈ K) :
    ∑ j ∈ K, (gridF N j - gridF N (j - m)) ^ 2 ≤ (m : ℝ) ^ 2 / (12 * (N : ℝ) ^ 2) := by
  have hZ := gridZ_pos hN
  have hval : ∀ j : ℤ, (gridF N j - gridF N (j - m)) ^ 2
      = (tent (gridM N) j - tent (gridM N) (j - m)) ^ 2 / gridZ N := by
    intro j
    rw [gridF, gridF, div_sub_div_same, div_pow, Real.sq_sqrt hZ.le]
  have htent : ∀ j : ℤ, tent (gridM N) j - tent (gridM N) (j - m) ≠ 0 → j ∈ K := by
    intro j hj
    refine hK j ?_
    rw [gridF, gridF, div_sub_div_same]
    exact div_ne_zero hj (Real.sqrt_ne_zero'.2 hZ)
  have hM : (gridM N : ℝ) = 6 * N := by
    rw [gridM]
    push_cast
    ring
  have hZval : gridZ N = 144 * (N : ℝ) ^ 3 + 2 * N := by
    have h3 := gridZ_mul_three N
    rw [hM] at h3
    ring_nf at h3
    linarith
  have hmul := mul_le_mul_of_nonneg_right (sum_tent_shift_sq_le (gridM N) m htent)
    (by positivity : (0 : ℝ) ≤ 12 * (N : ℝ) ^ 2)
  rw [hM] at hmul
  rw [Finset.sum_congr rfl (fun j _ => hval j), ← Finset.sum_div,
    div_le_div_iff₀ hZ (by positivity), hZval]
  nlinarith [hmul, sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) N]

end Komlos
