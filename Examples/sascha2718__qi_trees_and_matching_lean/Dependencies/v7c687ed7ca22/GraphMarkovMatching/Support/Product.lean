module
/-
The product of relations:

    Phi(R1 (x) R2, mu1 (x) mu2)  <=  Phi1 + Phi2 + 5 * Phi1 * Phi2

Mathlib has no `PMF.prod`, so `prodPMF` is built here from the `HasSum`
characterisation.

The constant `5` is `2 * alpha`, and the proof is: the good set of
`(x1,x2)` is a rectangle of mass `r1 * r2`, so `q = 1 - r1 r2 <= q1 + q2`,
whence `phi q <= phi q1 * r2^(-alpha) + phi q2 * r1^(-alpha)`; then apply
`rpow_neg_alpha_le` to each `r^(-alpha)` and use independence.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Potential
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X₁ X₂ : Type*}
/-! ### The product measure and the product relation -/
/-- The product PMF, `(μ₁ ⊗ μ₂)(x₁,x₂) = μ₁ x₁ · μ₂ x₂`. Not in Mathlib, so
constructed here: in `ℝ≥0∞` summability is automatic, so only the total mass
needs checking. -/
noncomputable def prodPMF (μ₁ : PMF X₁) (μ₂ : PMF X₂) : PMF (X₁ × X₂) :=
  ⟨fun p => μ₁ p.1 * μ₂ p.2, by
    have h : ∑' p : X₁ × X₂, μ₁ p.1 * μ₂ p.2 = 1 := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left, μ₂.tsum_coe, mul_one]
      exact μ₁.tsum_coe
    rw [← h]
    exact ENNReal.summable.hasSum⟩
@[simp] lemma prodPMF_apply (μ₁ : PMF X₁) (μ₂ : PMF X₂) (p : X₁ × X₂) :
    prodPMF μ₁ μ₂ p = μ₁ p.1 * μ₂ p.2 := rfl
lemma tsum_prod_split (f₁ : X₁ → ℝ≥0∞) (f₂ : X₂ → ℝ≥0∞) :
    ∑' p : X₁ × X₂, f₁ p.1 * f₂ p.2 = (∑' x, f₁ x) * (∑' y, f₂ y) := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
lemma toReal_rE_eq (μ : PMF X₁) (R : X₁ → X₁ → Prop) (x : X₁) :
    (rE μ R x).toReal = 1 - q μ R x := by
  have h := toReal_rE_add_toReal_qE μ R x
  rw [q]; linarith
end GraphMarkovMatching.Support
