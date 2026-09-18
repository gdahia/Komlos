/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Cube
public import Komlos.Transport

/-!
# A near-invariant distribution in the cube

This file proves Lemma 1.5 of Karingula–Lovett: for vectors lying on the grid `N⁻¹ • ℤ ^ d` and
of Euclidean norm at most `1`, there is a finitely supported probability distribution on the
cube `[-6, 6] ^ d`, with mean zero, whose shift distance at each of those vectors is at most
`1 / 3`.
-/

@[expose] public section

namespace Komlos

open Finset Finsupp

/-- The scaling `g ↦ g / N` from the integer lattice to the grid `N⁻¹ • ℤ ^ d`. -/
noncomputable def gridEmb (d N : ℕ) : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun g k := (g k : ℝ) / N
  map_zero' := by
    ext k
    simp
  map_add' g g' := by
    ext k
    simp only [Pi.add_apply]
    push_cast
    ring

@[simp] lemma gridEmb_apply (d N : ℕ) (g : Fin d → ℤ) (k : Fin d) :
    gridEmb d N g k = (g k : ℝ) / N := rfl

lemma gridEmb_injective {d N : ℕ} (hN : 0 < N) : Function.Injective (gridEmb d N) := by
  intro g g' hgg
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext k
  have hk := congrFun hgg k
  rw [gridEmb_apply, gridEmb_apply, div_eq_div_iff hN' hN'] at hk
  exact_mod_cast mul_right_cancel₀ hN' hk

lemma gridF_neg (N : ℕ) (j : ℤ) : gridF N (-j) = gridF N j := by
  rw [gridF, gridF, tent_neg]

lemma cubeP_neg (d N : ℕ) (g : Fin d → ℤ) : cubeP d N (-g) = cubeP d N g := by
  rw [cubeP_apply, cubeP_apply, cubeF, cubeF]
  congr 1
  congr with k
  rw [Pi.neg_apply, gridF_neg]

/-- **Lemma 1.5**: a mean-zero distribution in the cube `[-6, 6] ^ d` that is nearly invariant
under translation by any grid vector of Euclidean norm at most `1`. -/
theorem exists_nearInvariant {d N : ℕ} (hN : 0 < N) :
    ∃ P : (Fin d → ℝ) →₀ ℝ, IsDist P ∧ mean P = 0 ∧ (∀ x ∈ P.support, ∀ k, |x k| ≤ 6) ∧
      ∀ g : Fin d → ℤ, (∑ k, ((g k : ℝ) / N) ^ 2) ≤ 1 →
        shiftDist P (fun k => (g k : ℝ) / N) ≤ 3⁻¹ := by
  classical
  have hinj := gridEmb_injective (d := d) hN
  refine ⟨push (gridEmb d N) hinj (cubeP d N), (cubeP_isDist hN).push, ?_, ?_, ?_⟩
  · have hmem : ∀ g ∈ (cubeP d N).support, -g ∈ (cubeP d N).support := by
      intro g hg
      rw [Finsupp.mem_support_iff, cubeP_neg] at *
      exact hg
    have hself : mean (push (gridEmb d N) hinj (cubeP d N))
        = -mean (push (gridEmb d N) hinj (cubeP d N)) := by
      rw [mean_push, Finsupp.sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_nbij' (fun g => -g) (fun g => -g) hmem hmem (fun a _ => neg_neg a)
        (fun a _ => neg_neg a) (fun g _ => ?_)
      rw [cubeP_neg, map_neg, smul_neg, neg_neg]
    have h2 : (2 : ℝ) • mean (push (gridEmb d N) hinj (cubeP d N)) = 0 := by
      rw [two_smul]
      nth_rw 2 [hself]
      abel
    simpa using h2
  · intro x hx k
    rw [support_push, Finset.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hgk := cubeF_ne_zero_mem
      (g := g) (by simpa [cubeP_apply] using Finsupp.mem_support_iff.1 hg) k
    have hmem := gridF_ne_zero_mem hgk
    rw [Finset.mem_Icc] at hmem
    have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hbd : |(g k : ℝ)| ≤ 6 * N := by
      rw [gridM] at hmem
      have h1 : |g k| ≤ ((6 * N : ℕ) : ℤ) := abs_le.2 ⟨hmem.1, hmem.2⟩
      exact_mod_cast h1
    simp only [Function.Embedding.coeFn_mk, gridEmb_apply]
    rw [abs_div, abs_of_pos hN', div_le_iff₀ hN']
    linarith
  · intro g hg
    have hsd : shiftDist (push (gridEmb d N) hinj (cubeP d N)) (gridEmb d N g)
        = shiftDist (cubeP d N) g := shiftDist_push g (cubeP d N)
    have hsq := shiftDist_cubeP_sq_le (d := d) hN g
    have hnn : 0 ≤ shiftDist (cubeP d N) g := tvDist_nonneg _ _
    have : shiftDist (cubeP d N) g ≤ 3⁻¹ := by nlinarith
    rw [← hsd] at this
    exact this

end Komlos
