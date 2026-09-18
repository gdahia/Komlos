/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Split

/-!
# The pullback step

After splitting in the direction `v = 3 • w` and applying the inductive hypothesis, one obtains
a point `(z, β)` in the convex hull of the support of `split v P`. This file implements the
*pullback*: every state of `split v P` is sent back to available parents in `P`, which moves the
first component of the mean by exactly `e • w` for a sign `e`.
-/

@[expose] public section

namespace Komlos

open Finsupp Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Pullback step.** If `(z, β)` lies in the convex hull of the support of `split (3 • w) P`
and `β ≥ 1/3`, then `z + e • w` lies in the convex hull of the support of `P` for some sign `e`. -/
lemma pullback {P : E →₀ ℝ} (hP : IsDist P) (w : E) {β : ℝ} (hβ : 3⁻¹ ≤ β) {z : E}
    (hmem : ((z, β) : E × ℝ) ∈ convexHull ℝ ((split ((3 : ℝ) • w) P).support : Set (E × ℝ))) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ z + e • w ∈ convexHull ℝ (P.support : Set E) := by
  classical
  set v : E := (3 : ℝ) • w with hvdef
  set Q : (E × ℝ) →₀ ℝ := split v P with hQdef
  rw [Finset.mem_convexHull] at hmem
  obtain ⟨R, hR0, hR1, hRc⟩ := hmem
  rw [Finset.centerMass, hR1, inv_one, one_smul] at hRc
  simp only [id_eq] at hRc
  have hz : ∑ y ∈ Q.support, R y • y.1 = z := by
    have h := congrArg Prod.fst hRc
    rwa [Prod.fst_sum] at h
  have hb : ∑ y ∈ Q.support, R y * y.2 = β := by
    have h := congrArg Prod.snd hRc
    rw [Prod.snd_sum] at h
    simpa [smul_eq_mul] using h
  have hy2 : ∀ y ∈ Q.support, y.2 = 0 ∨ y.2 = 1 := by
    rintro ⟨x, b⟩ hy
    by_contra hcon
    rw [not_or] at hcon
    exact Finsupp.mem_support_iff.1 hy (split_apply_of_ne v P hcon.1 hcon.2 x)
  have hpar1 : ∀ y ∈ Q.support, y.2 = 1 → 0 < P (y.1 + v) ∧ 0 < P (y.1 - v) := by
    rintro ⟨x, b⟩ hy hb1
    simp only at hb1
    subst hb1
    rw [Finsupp.mem_support_iff, hQdef, split_apply_one] at hy
    exact lt_min_iff.1 (lt_of_le_of_ne (le_min (hP.nonneg _) (hP.nonneg _))
      (fun h => hy (by rw [← h, mul_zero])))
  have hpar0 : ∀ y ∈ Q.support, 0 < P (y.1 + v) ∨ 0 < P (y.1 - v) := by
    rintro ⟨x, b⟩ hy
    rcases hy2 _ hy with h | h
    · simp only at h
      subst h
      rw [Finsupp.mem_support_iff, hQdef, split_apply_zero] at hy
      exact lt_max_iff.1 (lt_of_le_of_ne (le_max_of_le_left (hP.nonneg _))
        (fun h => hy (by rw [← h, mul_zero])))
    · exact Or.inl (hpar1 _ hy h).1
  set σ : E × ℝ → ℝ := fun y => if 0 < P (y.1 + v) then 1 else 0 with hσdef
  set a₀ : ℝ := ∑ y ∈ Q.support, (1 - y.2) * (2 * σ y - 1) * R y with ha₀def
  set a : ℝ := 3 * a₀ with hadef
  set e : ℝ := if 0 ≤ a then 1 else -1 with hedef
  set t : ℝ := 2⁻¹ + (e - a) / (6 * β) with htdef
  set θ : E × ℝ → ℝ := fun y => y.2 * t + (1 - y.2) * σ y with hθdef
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have hsplit : ∑ y ∈ Q.support, (1 - y.2) * R y
      = (∑ y ∈ Q.support, R y) - ∑ y ∈ Q.support, R y * y.2 := by
    rw [← Finset.sum_sub_distrib]
    congr with y
    ring
  have hc : ∑ y ∈ Q.support, (1 - y.2) * R y = 1 - β := by rw [hsplit, hR1, hb]
  have hcnonneg : ∀ y ∈ Q.support, 0 ≤ (1 - y.2) * R y := by
    intro y hy
    rcases hy2 y hy with h | h <;> rw [h] <;> simp [hR0 y hy]
  have hβ1 : β ≤ 1 := by
    have := Finset.sum_nonneg hcnonneg
    linarith [hc ▸ this]
  have haabs : |a| ≤ 3 * (1 - β) := by
    rw [hadef, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), ← hc, ha₀def]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by norm_num)
    refine Finset.sum_le_sum fun y hy => ?_
    rcases hy2 y hy with h | h <;> rw [h] <;> simp only [hσdef] <;> split_ifs <;>
      norm_num [abs_of_nonneg (hR0 y hy)]
  have he1 : |e| = 1 := by rw [hedef]; split_ifs <;> norm_num
  have hea : |e - a| ≤ 1 := by
    rw [hedef]
    rcases abs_le.1 haabs with ⟨h1, h2⟩
    split_ifs with h <;> rw [abs_le] <;> constructor <;> linarith
  have htabs : |(e - a) / (6 * β)| ≤ 2⁻¹ := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 6 * β), div_le_iff₀ (by linarith)]
    linarith
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rcases abs_le.1 htabs with ⟨h1, h2⟩
    constructor <;> rw [htdef] <;> linarith
  have hσ01 : ∀ y, σ y = 0 ∨ σ y = 1 := by
    intro y
    simp only [hσdef]
    split_ifs <;> simp
  have hθ01 : ∀ y ∈ Q.support, 0 ≤ θ y ∧ θ y ≤ 1 := by
    intro y hy
    rcases hy2 y hy with h | h <;> simp only [hθdef, h] <;>
      rcases hσ01 y with hs | hs <;> rw [hs] <;> constructor <;>
      linarith [ht01.1, ht01.2]
  have hgamma : (∑ y ∈ Q.support, (2 * θ y - 1) * R y) * 3 = e := by
    have hexp : ∑ y ∈ Q.support, (2 * θ y - 1) * R y
        = (2 * t - 1) * (∑ y ∈ Q.support, R y * y.2) + a₀ := by
      rw [ha₀def, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr with y
      simp only [hθdef]
      ring
    rw [hexp, hb, htdef, hadef]
    field_simp
    ring
  set S : E →₀ ℝ := ∑ y ∈ Q.support,
    (Finsupp.single (y.1 + v) (θ y * R y) + Finsupp.single (y.1 - v) ((1 - θ y) * R y)) with hSdef
  have hmassterm : ∀ y ∈ Q.support,
      mass (Finsupp.single (y.1 + v) (θ y * R y) + Finsupp.single (y.1 - v) ((1 - θ y) * R y))
        = R y := by
    intro y _
    rw [mass_add, mass_single, mass_single]
    ring
  have hmeanterm : ∀ y ∈ Q.support,
      mean (Finsupp.single (y.1 + v) (θ y * R y) + Finsupp.single (y.1 - v) ((1 - θ y) * R y))
        = R y • y.1 + ((2 * θ y - 1) * R y) • v := by
    intro y _
    rw [mean_add, mean_single, mean_single]
    module
  have hSmass : mass S = 1 := by
    rw [hSdef, mass_finsetSum, Finset.sum_congr rfl hmassterm, hR1]
  have hSmean : mean S = z + e • w := by
    rw [hSdef, mean_finsetSum, Finset.sum_congr rfl hmeanterm, Finset.sum_add_distrib, hz,
      ← Finset.sum_smul, hvdef, smul_smul, hgamma]
  have hSapply : ∀ x : E, S x = ∑ y ∈ Q.support,
      (Finsupp.single (y.1 + v) (θ y * R y) x
        + Finsupp.single (y.1 - v) ((1 - θ y) * R y) x) := by
    intro x
    rw [hSdef, Finsupp.finsetSum_apply]
    congr
  have hSnonneg : ∀ x, 0 ≤ S x := by
    intro x
    rw [hSapply]
    refine Finset.sum_nonneg fun y hy => add_nonneg ?_ ?_ <;> rw [Finsupp.single_apply] <;>
      split_ifs
    · exact mul_nonneg (hθ01 y hy).1 (hR0 y hy)
    · exact le_rfl
    · exact mul_nonneg (by linarith [(hθ01 y hy).2]) (hR0 y hy)
    · exact le_rfl
  have hSsupp : S.support ⊆ P.support := by
    intro x hx
    by_contra hnot
    rw [Finsupp.mem_support_iff, hSapply] at hx
    have hPx : P x = 0 := Finsupp.notMem_support_iff.1 hnot
    refine hx (Finset.sum_eq_zero fun y hy => ?_)
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · rcases hpar0 y hy with h | h
      · rw [h1, hPx] at h
        exact absurd h (lt_irrefl 0)
      · rw [h2, hPx] at h
        exact absurd h (lt_irrefl 0)
    · have hnotone : y.2 ≠ 1 := by
        intro hone
        have h := (hpar1 y hy hone).1
        rw [h1, hPx] at h
        exact absurd h (lt_irrefl 0)
      have hy0 : y.2 = 0 := (hy2 y hy).resolve_right hnotone
      have hσy : σ y = 0 := by
        simp only [hσdef]
        rw [h1, hPx]
        simp
      simp only [hθdef, hy0, hσy]
      ring
    · have hnotone : y.2 ≠ 1 := by
        intro hone
        have h := (hpar1 y hy hone).2
        rw [h2, hPx] at h
        exact absurd h (lt_irrefl 0)
      have hy0 : y.2 = 0 := (hy2 y hy).resolve_right hnotone
      have hpos : 0 < P (y.1 + v) := by
        rcases hpar0 y hy with h | h
        · exact h
        · rw [h2, hPx] at h
          exact absurd h (lt_irrefl 0)
      have hσy : σ y = 1 := by
        simp only [hσdef]
        simp [hpos]
      simp only [hθdef, hy0, hσy]
      ring
    · ring
  refine ⟨e, ?_, ?_⟩
  · rw [hedef]
    split_ifs <;> simp
  · rw [← hSmean]
    exact mean_mem_convexHull ⟨hSnonneg, hSmass⟩ hSsupp

end Komlos
