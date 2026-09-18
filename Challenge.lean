import Mathlib

/-!
# Statements of the Komlós and Beck–Fiala bounds

The Komlós conjecture statement asks for signs on vectors of Euclidean norm at most `1` so that
every coordinate of their signed sum has absolute value at most `36`.
The Beck–Fiala conjecture statement asks for a vertex colouring of a finite hypergraph with edge
discrepancy at most `36 * √t`, where each vertex belongs to at most `t` edges.

The constants follow Karingula and Lovett, *An elementary proof of the Komlós conjecture*,
ECCC TR26-188 (2026). Proofs of these statements are in `Solution.lean`; this file contains
the challenge declarations.

The vector statement uses `EuclideanSpace ℝ κ` for the Euclidean norm. The hypergraph statement
uses Mathlib's `Hypergraph`, `finsum` for edge sums, and `Set.ncard` for vertex degrees.
-/

open Hypergraph

namespace Komlos

/-- The Komlós conjecture, with constant `36`: vectors of Euclidean norm at most `1` admit
signs whose signed sum has every coordinate bounded by `36` in absolute value. -/
theorem exists_sign_forall_abs_sum_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ k, |(∑ i, ε i • v i) k| ≤ 36 := by
  sorry

/-- The Beck–Fiala conjecture, with constant `36`: if every vertex of a hypergraph with
finitely many vertices lies in at most `t` edges, then some two-colouring of the vertices gives
every edge discrepancy at most `36 * √t`. -/
theorem exists_sign_forall_abs_finsum_le {α : Type*} {H : Hypergraph α} {t : ℕ}
    (hV : V(H).Finite) (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
      ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t := by
  sorry

end Komlos
