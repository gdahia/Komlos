/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Main

/-!
# The Beck–Fiala conjecture

The Beck–Fiala conjecture asserts that a hypergraph in which every vertex lies in at most `t`
edges admits a two-colouring of its vertices in which every edge has discrepancy `O(√t)`. It is
the special case of the Komlós conjecture in which the matrix is the incidence matrix of the
hypergraph, rescaled by `1 / √t` so that its columns have Euclidean norm at most `1`.

## Main definitions

* `Hypergraph.incidenceMatrix`: the edge–vertex incidence matrix of a hypergraph with finitely
  many vertices.

## Main results

* `Hypergraph.discrepancy_incidenceMatrix_le`: the incidence matrix has discrepancy at most
  `36 * √t`.
* `Hypergraph.exists_isColouring_forall_abs_finsum_le`: the same bound as a statement about
  colourings of the vertices.
-/

@[expose] public section

namespace Hypergraph

open Komlos Finset

variable {α : Type*} {H : Hypergraph α}

/-- A hypergraph with finitely many vertices has finitely many edges. -/
lemma edgeSet_finite (hV : V(H).Finite) : E(H).Finite :=
  hV.finite_subsets.subset edgeSet_subset_powerset_vertexSet

open Classical in
/-- The incidence matrix of a hypergraph with finitely many vertices: its rows are indexed by
the edges, its columns by the vertices, and an entry is `1` when the vertex lies in the edge
and `0` otherwise. -/
noncomputable def incidenceMatrix (H : Hypergraph α) (hV : V(H).Finite) :
    Matrix (edgeSet_finite hV).toFinset hV.toFinset ℝ :=
  Matrix.of fun e x => if (x : α) ∈ (e : Set α) then 1 else 0

open Classical in
lemma incidenceMatrix_apply (hV : V(H).Finite) (e : (edgeSet_finite hV).toFinset)
    (x : hV.toFinset) :
    H.incidenceMatrix hV e x = if (x : α) ∈ (e : Set α) then 1 else 0 := rfl

/-- **The Beck–Fiala conjecture**, with constant `36`: if every vertex of a hypergraph lies in at
most `t` edges, then its incidence matrix has discrepancy at most `36 * √t`. -/
theorem discrepancy_incidenceMatrix_le {t : ℕ} (hV : V(H).Finite)
    (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    discrepancy (H.incidenceMatrix hV) ≤ 36 * Real.sqrt t := by
  classical
  have hdegS : ∀ x : hV.toFinset,
      ((edgeSet_finite hV).toFinset.filter fun e => (x : α) ∈ e).card ≤ t := by
    intro x
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    convert hdeg x ((Set.Finite.mem_toFinset hV).1 x.2) using 2
    ext e
    simp
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine discrepancy_le_iff.2 ⟨ofBool fun _ => true, isColouring_ofBool _, ?_⟩
    rw [colouringDiscrepancy_le_iff (by simp)]
    intro e
    have hzero : ∀ x : hV.toFinset, H.incidenceMatrix hV e x = 0 := by
      intro x
      rw [incidenceMatrix_apply, ite_eq_right]
      intro hx
      have hcard := hdegS x
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hcard
      exact hcard e (Finset.mem_filter.2 ⟨e.2, hx⟩)
    simp [hzero]
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 htR
    have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt htR.le
    have hcol : ∀ x, ∑ e, ((Real.sqrt t)⁻¹ • H.incidenceMatrix hV) e x ^ 2 ≤ 1 := by
      intro x
      have hterm : ∀ e : (edgeSet_finite hV).toFinset,
          ((Real.sqrt t)⁻¹ • H.incidenceMatrix hV) e x ^ 2
            = (if (x : α) ∈ (e : Set α) then 1 else 0) / t := by
        intro e
        rw [Matrix.smul_apply, smul_eq_mul, incidenceMatrix_apply]
        split_ifs
        · rw [mul_one, inv_pow, hs2, one_div]
        · simp
      rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_div,
        Finset.sum_coe_sort (edgeSet_finite hV).toFinset
          (fun e => if (x : α) ∈ e then (1 : ℝ) else 0),
        Finset.sum_boole, div_le_one htR]
      exact_mod_cast hdegS x
    obtain ⟨ε, hε, hbd⟩ :=
      discrepancy_le_iff.1 (discrepancy_le_of_forall_sum_sq_le_one _ hcol)
    refine discrepancy_le_iff.2 ⟨ε, hε, ?_⟩
    rw [colouringDiscrepancy_le_iff (by norm_num)] at hbd
    rw [colouringDiscrepancy_le_iff (by positivity)]
    intro e
    have he := hbd e
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at he
    rw [abs_mul, abs_of_pos (inv_pos.2 hs), inv_mul_le_iff₀ hs] at he
    linarith

/-- **The Beck–Fiala conjecture**, colouring form: if every vertex of a hypergraph lies in at
most `t` edges, then some colouring of the vertices gives every edge discrepancy at most
`36 * √t`. -/
theorem exists_isColouring_forall_abs_finsum_le {t : ℕ} (hV : V(H).Finite)
    (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, IsColouring χ ∧ ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t := by
  classical
  obtain ⟨ε, hε, hbd⟩ := discrepancy_le_iff.1 (discrepancy_incidenceMatrix_le hV hdeg)
  rw [colouringDiscrepancy_le_iff (by positivity)] at hbd
  set χ : α → ℝ := fun x => if hx : x ∈ hV.toFinset then ε ⟨x, hx⟩ else 1 with hχ
  have hχpos : ∀ x (hx : x ∈ hV.toFinset), χ x = ε ⟨x, hx⟩ := fun x hx => by
    rw [hχ]
    exact dite_eq_left hx
  have hχneg : ∀ x, x ∉ hV.toFinset → χ x = 1 := fun x hx => by
    rw [hχ]
    exact dite_eq_right hx
  refine ⟨χ, fun x => ?_, fun e he => ?_⟩
  · by_cases hx : x ∈ hV.toFinset
    · rw [hχpos x hx]
      exact hε _
    · rw [hχneg x hx]
      exact Or.inl rfl
  · have hmem : e ∈ (edgeSet_finite hV).toFinset := by simpa using he
    have hfin : e.Finite := hV.subset (subset_vertexSet_of_mem_edgeSet he)
    have hεχ : ∀ x : hV.toFinset, ε x = χ x := fun x => (hχpos x x.2).symm
    have hfilter : hV.toFinset.filter (· ∈ e) = hfin.toFinset := by
      ext x
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨subset_vertexSet_of_mem_edgeSet he h, h⟩⟩
    have hsum : ∑ x, H.incidenceMatrix hV ⟨e, hmem⟩ x * ε x = ∑ᶠ x ∈ e, χ x := by
      rw [Finset.sum_congr rfl fun x _ => by rw [incidenceMatrix_apply, hεχ x],
        Finset.sum_coe_sort hV.toFinset (fun y => (if y ∈ e then (1 : ℝ) else 0) * χ y),
        finsum_mem_eq_finite_toFinset_sum _ hfin, ← hfilter, Finset.sum_filter]
      congr with y
      split_ifs <;> simp
    rw [← hsum]
    exact hbd ⟨e, hmem⟩

end Hypergraph
