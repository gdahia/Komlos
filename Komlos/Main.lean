/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Komlos.Approximation
public import Komlos.GridCase

/-!
# The Komlós conjecture

The main theorem: a real matrix whose columns have Euclidean norm at most `1` has discrepancy
at most `36`. Equivalently, vectors `v₁, …, vₙ ∈ ℝ ^ d` of Euclidean norm at most `1` admit signs
`εᵢ ∈ {-1, 1}` with `‖∑ i, εᵢ • vᵢ‖_∞ ≤ 36`.

The grid case is `Komlos.discrepancy_le_of_grid`. For a general matrix, approximate its columns
by grid vectors to within `η / (n + 1)` in each coordinate: a colouring witnessing the grid
bound then has discrepancy at most `36 + η` on the original matrix.
-/

@[expose] public section

namespace Komlos

open Finset Matrix

/-- **Theorem 1.2** for matrices with rows indexed by `Fin d` and columns indexed by `Fin n`. -/
theorem discrepancy_le_of_forall_sum_sq_le_one_fin {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 1) : discrepancy A ≤ 36 := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨N, g, hNpos, happ1, happ2⟩ :=
    exists_grid_approx (fun j i => A i j) (by positivity : 0 < η / (n + 1))
  have hnorm : ∀ j, ∑ i, ((g j i : ℝ) / N) ^ 2 ≤ 1 := by
    intro j
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hA j)
    nlinarith [happ1 j i, abs_nonneg ((g j i : ℝ) / N), abs_nonneg (A i j),
      sq_abs ((g j i : ℝ) / N), sq_abs (A i j)]
  obtain ⟨ε, hε, hbd⟩ := discrepancy_le_iff.1 (discrepancy_le_of_grid hNpos g hnorm)
  refine discrepancy_le_iff.2 ⟨ε, hε, ?_⟩
  rw [colouringDiscrepancy_le_iff (by norm_num)] at hbd
  rw [colouringDiscrepancy_le_iff (by positivity)]
  intro i
  have hsplit : ∑ j, A i j * ε j
      = (∑ j, Matrix.of (fun (k : Fin d) (j : Fin n) => (g j k : ℝ) / N) i j * ε j)
        + ∑ j, (A i j - (g j i : ℝ) / N) * ε j := by
    rw [← Finset.sum_add_distrib]
    congr with j
    rw [Matrix.of_apply]
    ring
  have htail : |∑ j, (A i j - (g j i : ℝ) / N) * ε j| ≤ η := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ : Fin n => η / (n + 1)) fun j _ => ?_).trans ?_
    · rw [abs_mul, (by rcases hε j with h | h <;> rw [h] <;> norm_num : |ε j| = 1), mul_one]
      exact happ2 j i
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc',
        div_le_iff₀ (by positivity)]
      nlinarith
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith [hbd i])

/-- **Theorem 1.2** (Komlós conjecture, with constant `36`): a real matrix whose columns have
Euclidean norm at most `1` has discrepancy at most `36`. -/
theorem discrepancy_le_of_forall_sum_sq_le_one {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 1) : discrepancy A ≤ 36 := by
  classical
  obtain ⟨ε, hε, hbd⟩ := discrepancy_le_iff.1 (discrepancy_le_of_forall_sum_sq_le_one_fin
    (Matrix.of fun a b => A ((Fintype.equivFin m).symm a) ((Fintype.equivFin n).symm b))
    fun b => by
      simp only [Matrix.of_apply]
      rw [Equiv.sum_comp (Fintype.equivFin m).symm
        fun i => A i ((Fintype.equivFin n).symm b) ^ 2]
      exact hA _)
  refine discrepancy_le_iff.2 ⟨fun j => ε (Fintype.equivFin n j), fun j => hε _, ?_⟩
  rw [colouringDiscrepancy_le_iff (by norm_num)] at hbd ⊢
  intro i
  have hi := hbd (Fintype.equivFin m i)
  simp only [Matrix.of_apply, Equiv.symm_apply_apply] at hi
  rw [← Equiv.sum_comp (Fintype.equivFin n)
    fun b => A i ((Fintype.equivFin n).symm b) * ε b] at hi
  simpa using hi

/-- **Theorem 1.2**, Euclidean form: if `v i ∈ ℝ ^ κ` have Euclidean norm at most `1`, then the
matrix with columns `v i` has discrepancy at most `36`. -/
theorem discrepancy_le_of_forall_norm_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    discrepancy (Matrix.of fun k i => v i k) ≤ 36 := by
  refine discrepancy_le_of_forall_sum_sq_le_one _ fun i => ?_
  have hnn : (0 : ℝ) ≤ ∑ k, ‖v i k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hvi := hv i
  rw [EuclideanSpace.norm_eq] at hvi
  have hsq : ∑ k, ‖v i k‖ ^ 2 ≤ 1 := by
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∑ k, ‖v i k‖ ^ 2)]
  refine le_trans (le_of_eq ?_) hsq
  congr with k
  rw [Matrix.of_apply, Real.norm_eq_abs, sq_abs]

/-- **Theorem 1.2**, colouring form: vectors of Euclidean norm at most `1` admit a colouring whose
signed sum has every coordinate bounded by `36`. -/
theorem exists_isColouring_forall_abs_sum_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : ι → ℝ, IsColouring ε ∧ ∀ k, |(∑ i, ε i • v i) k| ≤ 36 := by
  obtain ⟨ε, hε, hbd⟩ := discrepancy_le_iff.1 (discrepancy_le_of_forall_norm_le_one v hv)
  rw [colouringDiscrepancy_le_iff (by norm_num)] at hbd
  refine ⟨ε, hε, fun k => ?_⟩
  simpa [mul_comm] using hbd k

end Komlos
