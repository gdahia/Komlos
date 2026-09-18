import Komlos

/-!
# Proved solution

The statements advertised in `Challenge.lean`, proved from the `Komlos` library, where they are
stated in terms of `Komlos.discrepancy` and `Komlos.IsColouring`.

* `Komlos.exists_isColouring_mean_add_sum_mem_convexHull` is Lemma 1.4 of the source paper.
* `Komlos.exists_nearInvariant` is Lemma 1.5.
* `Komlos.discrepancy_le_of_forall_sum_sq_le_one` is Theorem 1.2.
* `Hypergraph.discrepancy_incidenceMatrix_le` is its Beck–Fiala consequence.
-/

open Hypergraph

namespace Komlos

/-- **The Komlós conjecture**, with constant `36`: vectors of Euclidean norm at most `1` admit
signs whose signed sum has every coordinate bounded by `36` in absolute value. -/
theorem exists_sign_forall_abs_sum_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ k, |(∑ i, ε i • v i) k| ≤ 36 :=
  exists_isColouring_forall_abs_sum_apply_le v hv

/-- **The Beck–Fiala conjecture**, with constant `36`: if every vertex of a hypergraph with
finitely many vertices lies in at most `t` edges, then some two-colouring of the vertices gives
every edge discrepancy at most `36 * √t`. -/
theorem exists_sign_forall_abs_finsum_le {α : Type*} {H : Hypergraph α} {t : ℕ}
    (hV : V(H).Finite) (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
      ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t :=
  exists_isColouring_forall_abs_finsum_le hV hdeg

end Komlos
