module
/-
The facts of the one-law contraction lemma that the restricted four-law
and its callers reuse:

* `ennreal_add_sq_le_weighted`: the weighted mean inequality
  `(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` in `ℝ≥0∞`, for real `δ > 0`;
* `q_sq_le`: the `K`-step `q² ≤ K·φ_α(q)` on `[0,1)`, for every `K` with
  `t(1-t)^α ≤ K` on `[0,1]`;
* `cOverlap_le_one`, `aOverlap_ne_top`, `cOverlap_ne_top`: the overlap
  degrees are at most one, hence finite.

The contraction lemma itself, with its pointwise split and averaging
machinery, is kept in `Archive/Support/Contraction.lean`.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Square
@[expose] public section
namespace GraphMarkovMatching.Support
open Real
open scoped ENNReal Classical
/-! ### ℝ≥0∞ arithmetic helper -/
variable {X : Type*}
end GraphMarkovMatching.Support
