import Komlos

/-!
# Proofs of the challenge statements

The two theorems in `Challenge.lean` follow from the colouring bounds in the `Komlos` library.
The proof uses Lemmas 1.4 and 1.5 of Karingula–Lovett to obtain the matrix bound in Theorem 1.2.
Applying the scaled matrix bound to an incidence matrix gives the Beck–Fiala bound.
-/

open Hypergraph

namespace Komlos

/-- The Komlós conjecture, with constant `36`: vectors of Euclidean norm at most `1` admit
signs whose signed sum has every coordinate bounded by `36` in absolute value. -/
theorem exists_sign_forall_abs_sum_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → EuclideanSpace ℝ κ) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ k, |(∑ i, ε i • v i) k| ≤ 36 :=
  exists_isColouring_forall_abs_sum_apply_le v hv

/-- The Beck–Fiala conjecture, with constant `36`: if every vertex of a hypergraph with
finitely many vertices lies in at most `t` edges, then some two-colouring of the vertices gives
every edge discrepancy at most `36 * √t`. -/
theorem exists_sign_forall_abs_finsum_le {α : Type*} {H : Hypergraph α} {t : ℕ}
    (hV : V(H).Finite) (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
      ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t :=
  exists_isColouring_forall_abs_finsum_le hV hdeg

end Komlos
