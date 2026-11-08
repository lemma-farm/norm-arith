module
/-
The symmetrised square `R^□` of a relation and the setup for the
contraction lemma.

This file fixes the definitions and the structural facts:

* `SquareRel`      the symmetrised square relation on `X × X`
* refl / symm      preserved from `R`, as required to feed `R^□` back into
                   the contraction
* `aOverlap`       `a = μ{y : x₀ R y ∧ x₁ R y}`, the both-compatible overlap
* `cOverlap`       `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`, the neither-compatible mass
* `aOverlap_le_rE` `a ≤ r_i`, since a single `Y` compatible with both is in
                   particular compatible with each (so `a ≤ min(r₀,r₁)`)

The degree identities and the contraction estimate itself are in
`Contraction.lean`.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v1728b582a71a.GraphMarkovMatching.Support.Product
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X : Type*}
/-! ### The symmetrised square, equation (11.13) -/
/-- The symmetrised square `R^□` of equation (11.13):
`(x₀,x₁) R^□ (y₀,y₁) ↔ (x₀ R y₀ ∧ x₁ R y₁) ∨ (x₀ R y₁ ∧ x₁ R y₀)`.

The second disjunct crosses the coordinates; this is what distinguishes `R^□`
from the tensor square `ProdRel R R`, and it is exactly the "good antidiagonal"
of the transversal Lemma 11.4. -/
def SquareRel (R : X → X → Prop) : X × X → X × X → Prop :=
  fun x y => (R x.1 y.1 ∧ R x.2 y.2) ∨ (R x.1 y.2 ∧ R x.2 y.1)
noncomputable def aOverlap (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) : ℝ≥0∞ :=
  ∑' y, if R x₀ y ∧ R x₁ y then μ y else 0
/-- The paper's `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`: the mass of labels incompatible
with both. This is the per-column bad probability in the transversal argument. -/
noncomputable def cOverlap (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) : ℝ≥0∞ :=
  ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0
/-- `a ≤ r₀`: a label compatible with both `x₀` and `x₁` is in particular
compatible with `x₀`. Half of `a ≤ min(r₀,r₁)`. -/
lemma aOverlap_le_rE_left (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≤ rE μ R x₀ := by
  rw [aOverlap, rE]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : R x₀ y ∧ R x₁ y
  · simp [h]
  · simp only [h, ite_false]; positivity
/-- `a ≤ r₁`, the other half of `a ≤ min(r₀,r₁)`. -/
lemma aOverlap_le_rE_right (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≤ rE μ R x₁ := by
  rw [aOverlap, rE]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : R x₀ y ∧ R x₁ y
  · simp [h]
  · simp only [h, ite_false]; positivity
end GraphMarkovMatching.Support
