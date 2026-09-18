# Komlós

A Lean 4 and Mathlib formalization of the **Komlós conjecture** with explicit constant `36`,
following S. R. Karingula and S. Lovett, [*An elementary proof of the Komlós
conjecture*](https://eccc.weizmann.ac.il/report/2026/188/), ECCC TR26-188 (2026), and of the
**Beck–Fiala conjecture** as a consequence.

## Main results

The advertised statements are in [`Challenge.lean`](Challenge.lean) and are proved in
[`Solution.lean`](Solution.lean).

* `Komlos.exists_sign_forall_abs_sum_apply_le`: vectors `v i : EuclideanSpace ℝ κ` with
  `‖v i‖ ≤ 1` admit signs `ε i ∈ {-1, 1}` with `|(∑ i, ε i • v i) k| ≤ 36` for every
  coordinate `k`.
* `Komlos.exists_sign_forall_abs_finsum_le`: a Mathlib `Hypergraph` with finitely many vertices,
  each lying in at most `t` edges, admits a two-colouring `χ` with `|∑ᶠ x ∈ e, χ x| ≤ 36 * √t`
  for every edge `e`.

In the library these are stated with `Komlos.discrepancy`, the discrepancy of a matrix: a real
matrix whose columns have Euclidean norm at most `1` has discrepancy at most `36`
(`Komlos.discrepancy_le_of_forall_sum_sq_le_one`), and the incidence matrix of a hypergraph of
degree at most `t` has discrepancy at most `36 * √t`
(`Hypergraph.discrepancy_incidenceMatrix_le`).

## Layout

| Module | Contents |
| --- | --- |
| `Komlos.Discrepancy` | colourings, the discrepancy of a colouring and of a matrix |
| `Komlos.Distribution` | finitely supported distributions, mass and mean |
| `Komlos.Translation` | translation of distributions |
| `Komlos.ShiftDistance` | total variation, overlap and shift distance |
| `Komlos.Split` | the splitting operator and Claim 3.2 |
| `Komlos.Pullback` | the pullback step |
| `Komlos.SignedSums` | Lemma 1.4 |
| `Komlos.Tent` | the discrete tent and its energy bound |
| `Komlos.Grid` | the normalised one-dimensional grid weight |
| `Komlos.Hellinger` | total variation bounded by the `L²` distance of square roots |
| `Komlos.Cube` | the product distribution on the integer grid |
| `Komlos.Transport` | pushing distributions along injective additive maps |
| `Komlos.NearInvariant` | Lemma 1.5 |
| `Komlos.GridCase` | Theorem 1.2 for grid vectors |
| `Komlos.Approximation` | approximating real vectors by grid vectors |
| `Komlos.Main` | Theorem 1.2 |
| `Komlos.BeckFiala` | the Beck–Fiala conjecture |

The library uses the Lean module system. The proof of Lemma 1.5 is a discrete variant of the
one in the source; see `fidelity` in [`formalization.yaml`](formalization.yaml).

## Building

```sh
lake exe cache get
lake build
```
