/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Grid
public import Komlos.Hellinger

/-!
# The near-invariant distribution on the integer grid

`Komlos.cubeP d N` is the product of `d` copies of the normalised squared tent `gridF N ^ 2`,
viewed as a distribution on `Fin d → ℤ`. Because it is a product and translations act
coordinatewise, the `L²` distance between the square roots of `cubeP` and of its translate
tensorises, and the one-dimensional estimate `Komlos.sum_gridF_shift_sq_le` gives

`shiftDist (cubeP d N) h ^ 2 ≤ (∑ k, (h k / N) ^ 2) / 12`.
-/

@[expose] public section

namespace Komlos

open Finset Finsupp

/-- The `d`-dimensional product weight on the integer grid. -/
noncomputable def cubeF (d N : ℕ) (g : Fin d → ℤ) : ℝ := ∏ k, gridF N (g k)

lemma cubeF_nonneg (d N : ℕ) (g : Fin d → ℤ) : 0 ≤ cubeF d N g :=
  Finset.prod_nonneg fun k _ => gridF_nonneg N (g k)

lemma cubeF_ne_zero_mem {d N : ℕ} {g : Fin d → ℤ} (h : cubeF d N g ≠ 0) (k : Fin d) :
    gridF N (g k) ≠ 0 := fun hk => h (Finset.prod_eq_zero (Finset.mem_univ k) hk)

/-- The near-invariant distribution on the integer grid. -/
noncomputable def cubeP (d N : ℕ) : (Fin d → ℤ) →₀ ℝ :=
  Finsupp.onFinset (Fintype.piFinset fun _ => Finset.Icc (-(gridM N : ℤ)) (gridM N))
    (fun g => cubeF d N g ^ 2)
    (by
      intro g hg
      rw [Fintype.mem_piFinset]
      exact fun k => gridF_ne_zero_mem (cubeF_ne_zero_mem (by grind) k))

@[simp] lemma cubeP_apply (d N : ℕ) (g : Fin d → ℤ) : cubeP d N g = cubeF d N g ^ 2 :=
  Finsupp.onFinset_apply

/-- Fubini for a product over a `piFinset`. -/
lemma sum_prod_piFinset (d : ℕ) (K : Finset ℤ) (φ : Fin d → ℤ → ℝ) :
    ∑ g ∈ Fintype.piFinset fun _ : Fin d => K, ∏ k, φ k (g k) = ∏ k, ∑ j ∈ K, φ k j :=
  (Finset.prod_univ_sum _ _).symm

lemma cubeP_support_subset {d N : ℕ} {K : Finset ℤ} (hK : ∀ j, gridF N j ≠ 0 → j ∈ K) :
    (cubeP d N).support ⊆ Fintype.piFinset fun _ : Fin d => K := by
  intro g hg
  rw [Finsupp.mem_support_iff, cubeP_apply] at hg
  rw [Fintype.mem_piFinset]
  exact fun k => hK _ (cubeF_ne_zero_mem (by grind) k)

lemma sum_cubeF_sq {d N : ℕ} (hN : 0 < N) {K : Finset ℤ} (hK : ∀ j, gridF N j ≠ 0 → j ∈ K) :
    ∑ g ∈ Fintype.piFinset fun _ : Fin d => K, cubeF d N g ^ 2 = 1 := by
  have hterm : ∀ g : Fin d → ℤ, cubeF d N g ^ 2 = ∏ k, gridF N (g k) ^ 2 := by
    intro g
    rw [cubeF, Finset.prod_pow]
  rw [Finset.sum_congr rfl (fun g _ => hterm g),
    sum_prod_piFinset d K (fun _ j => gridF N j ^ 2),
    Finset.prod_congr rfl (fun k _ => sum_gridF_sq hN hK), Finset.prod_const_one]

lemma cubeP_isDist {d N : ℕ} (hN : 0 < N) : IsDist (cubeP d N) where
  nonneg g := by
    rw [cubeP_apply]
    positivity
  mass_eq := by
    rw [mass_eq_sum (cubeP_support_subset (fun j hj => gridF_ne_zero_mem hj)),
      Finset.sum_congr rfl (fun g _ => cubeP_apply d N g)]
    exact sum_cubeF_sq hN fun j hj => gridF_ne_zero_mem hj

/-- **The tensorised shift estimate.** The `L²` distance between the square roots of `cubeP`
and of its translate by `h` is controlled coordinatewise, so the total variation distance
satisfies `shiftDist (cubeP d N) h ^ 2 ≤ ‖h / N‖₂ ^ 2 / 12`. -/
lemma shiftDist_cubeP_sq_le {d N : ℕ} (hN : 0 < N) (h : Fin d → ℤ) :
    shiftDist (cubeP d N) h ^ 2 ≤ (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
  classical
  set B : ℤ := ∑ k, |h k| with hBdef
  set K : Finset ℤ := Finset.Icc (-((gridM N : ℤ) + B)) ((gridM N : ℤ) + B) with hKdef
  set T : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => K with hTdef
  have hBk : ∀ k, |h k| ≤ B := fun k =>
    Finset.single_le_sum (f := fun k => |h k|) (fun i _ => abs_nonneg _) (Finset.mem_univ k)
  have hKmem : ∀ j : ℤ, |j| ≤ (gridM N : ℤ) + B → j ∈ K := by
    intro j hj
    rw [hKdef, Finset.mem_Icc]
    rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at hj <;> grind
  have hgK : ∀ j, gridF N j ≠ 0 → j ∈ K := by
    intro j hj
    have hmem := gridF_ne_zero_mem hj
    rw [Finset.mem_Icc] at hmem
    refine hKmem j ?_
    have hB0 : (0 : ℤ) ≤ B := Finset.sum_nonneg fun k _ => abs_nonneg _
    rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> grind
  have hgKs : ∀ (k : Fin d) (j : ℤ), gridF N (j - h k) ≠ 0 → j ∈ K := by
    intro k j hj
    have hmem := gridF_ne_zero_mem hj
    rw [Finset.mem_Icc] at hmem
    have h2 := hBk k
    refine hKmem j ?_
    rcases abs_cases j with ⟨e, _⟩ | ⟨e, _⟩ <;> rcases abs_cases (h k) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rw [e] <;> rw [e2] at h2 <;> grind
  have hgKd : ∀ (k : Fin d) (j : ℤ), gridF N j - gridF N (j - h k) ≠ 0 → j ∈ K := by
    intro k j hj
    rcases eq_or_ne (gridF N j) 0 with hz | hz
    · exact hgKs k j (by grind)
    · exact hgK j hz
  have hP := cubeP_isDist (d := d) (N := N) hN
  have hPs : (cubeP d N).support ⊆ T := cubeP_support_subset hgK
  have hQs : (tr h (cubeP d N)).support ⊆ T := by
    intro g hg
    rw [Finsupp.mem_support_iff, tr_apply, cubeP_apply] at hg
    rw [hTdef, Fintype.mem_piFinset]
    intro k
    refine hgKs k (g k) ?_
    simpa using cubeF_ne_zero_mem (g := g - h) (by grind) k
  have hmain := tvDist_sq_le hP (hP.tr h) hPs hQs (fun g => cubeF d N g)
    (fun g => cubeF d N (g - h)) (cubeF_nonneg d N) (fun g => cubeF_nonneg d N (g - h))
    (fun g _ => cubeP_apply d N g) (fun g _ => by rw [tr_apply, cubeP_apply])
  set A : Fin d → ℝ := fun k => ∑ j ∈ K, gridF N j * gridF N (j - h k) with hAdef
  set a : Fin d → ℝ := fun k => 1 - A k with hadef
  have hshiftsum : ∀ k : Fin d, ∑ j ∈ K, gridF N (j - h k) ^ 2 = 1 := by
    intro k
    rw [hKdef, ← sum_shift_index (fun j => gridF N j ^ 2) (h k)]
    refine sum_gridF_sq hN fun j hj => ?_
    have hmem := gridF_ne_zero_mem hj
    rw [Finset.mem_Icc] at hmem ⊢
    have h2 := hBk k
    rcases abs_cases (h k) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e2] at h2 <;> grind
  have hsq : ∀ k : Fin d, ∑ j ∈ K, (gridF N j - gridF N (j - h k)) ^ 2 = 2 * a k := by
    intro k
    have hexp : ∀ j : ℤ, (gridF N j - gridF N (j - h k)) ^ 2
        = gridF N j ^ 2 - 2 * (gridF N j * gridF N (j - h k)) + gridF N (j - h k) ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_gridF_sq hN hgK, hshiftsum k, hadef, hAdef]
    ring
  have ha0 : ∀ k, 0 ≤ a k := by
    intro k
    have hnn := Finset.sum_nonneg
      (fun j (_ : j ∈ K) => sq_nonneg (gridF N j - gridF N (j - h k)))
    rw [hsq k] at hnn
    linarith
  have ha1 : ∀ k, a k ≤ 1 := by
    intro k
    have hnn : 0 ≤ A k :=
      Finset.sum_nonneg fun j _ => mul_nonneg (gridF_nonneg _ _) (gridF_nonneg _ _)
    rw [hadef]
    simp only
    linarith
  have hS3 : ∑ g ∈ T, cubeF d N (g - h) ^ 2 = 1 := by
    have hterm : ∀ g : Fin d → ℤ, cubeF d N (g - h) ^ 2 = ∏ k, gridF N (g k - h k) ^ 2 := by
      intro g
      rw [cubeF, Finset.prod_pow]
      congr
    rw [hTdef, Finset.sum_congr rfl (fun g _ => hterm g),
      sum_prod_piFinset d K (fun k j => gridF N (j - h k) ^ 2),
      Finset.prod_congr rfl (fun k _ => hshiftsum k), Finset.prod_const_one]
  have hS2 : ∑ g ∈ T, cubeF d N g * cubeF d N (g - h) = ∏ k, A k := by
    have hterm : ∀ g : Fin d → ℤ, cubeF d N g * cubeF d N (g - h)
        = ∏ k, gridF N (g k) * gridF N (g k - h k) := by
      intro g
      rw [cubeF, cubeF, ← Finset.prod_mul_distrib]
      congr
    rw [hTdef, Finset.sum_congr rfl (fun g _ => hterm g),
      sum_prod_piFinset d K (fun k j => gridF N j * gridF N (j - h k))]
  have hexpand : ∑ g ∈ T, (cubeF d N g - cubeF d N (g - h)) ^ 2 = 2 - 2 * ∏ k, A k := by
    have hterm : ∀ g : Fin d → ℤ, (cubeF d N g - cubeF d N (g - h)) ^ 2
        = cubeF d N g ^ 2 - 2 * (cubeF d N g * cubeF d N (g - h)) + cubeF d N (g - h) ^ 2 :=
      fun g => by ring
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_cubeF_sq hN hgK, hS2, hS3]
    ring
  have haA : ∀ k, (1 : ℝ) - a k = A k := by
    intro k
    simp only [hadef]
    ring
  have hweier : 1 - ∑ k, a k ≤ ∏ k, A k := by
    have hw := one_sub_sum_le_prod Finset.univ a (fun k _ => ha0 k) (fun k _ => ha1 k)
    rwa [Finset.prod_congr rfl (fun k _ => haA k)] at hw
  have hasum : ∑ k, 2 * a k ≤ ∑ k, ((h k : ℝ) ^ 2 / (12 * (N : ℝ) ^ 2)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← hsq k]
    exact sum_gridF_shift_sq_le hN (h k) (hgKd k)
  have hfinal : ∑ k, ((h k : ℝ) ^ 2 / (12 * (N : ℝ) ^ 2)) = (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
    rw [Finset.sum_div]
    congr with k
    rw [div_pow]
    ring
  rw [shiftDist]
  refine hmain.trans ?_
  rw [hexpand, ← hfinal]
  rw [← Finset.mul_sum] at hasum
  linarith [hasum, hweier]

end Komlos
