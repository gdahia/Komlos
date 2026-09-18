import Mathlib

/-!
# The Komlós and Beck–Fiala conjectures

**Komlós conjecture.** There is a universal constant `C` such that any vectors `vᵢ` of Euclidean
norm at most `1` admit signs `εᵢ ∈ {-1, 1}` with `‖∑ i, εᵢ • vᵢ‖_∞ ≤ C`.

**Beck–Fiala conjecture.** A hypergraph in which every vertex lies in at most `t` edges admits a
two-colouring `χ` of its vertices with `|∑ x ∈ e, χ x| = O(√t)` for every edge `e`.

Both are stated with the explicit constant `36`, following S. R. Karingula and S. Lovett,
*An elementary proof of the Komlós conjecture*, ECCC TR26-188 (2026).

In the Komlós statement the vectors are `v i : EuclideanSpace ℝ κ`, so `‖v i‖` is the Euclidean
norm, and the conclusion bounds every coordinate `k` of the signed sum, that is, its supremum
norm. The Beck–Fiala statement uses Mathlib's `Hypergraph`; the sum over an edge `e : Set α` is
the finite sum `∑ᶠ x ∈ e, χ x`, and the degree of a vertex `x` is the number of edges containing
it.
-/

open Hypergraph

namespace Komlos

/-- **The Komlós conjecture**, with constant `36`: vectors of Euclidean norm at most `1` admit
signs whose signed sum has every coordinate bounded by `36` in absolute value. -/
theorem exists_sign_forall_abs_sum_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ k, |(∑ i, ε i • v i) k| ≤ 36 := by
  sorry

/-- **The Beck–Fiala conjecture**, with constant `36`: if every vertex of a hypergraph with
finitely many vertices lies in at most `t` edges, then some two-colouring of the vertices gives
every edge discrepancy at most `36 * √t`. -/
theorem exists_sign_forall_abs_finsum_le {α : Type*} {H : Hypergraph α} {t : ℕ}
    (hV : V(H).Finite) (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
      ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t := by
  sorry

end Komlos
