module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourHolderNorm
/-!
# Actual conjugation, multiplication and reciprocals of Hölder functions

All operations are the literal pointwise complex operations.  In the inherited
max norm multiplication is bounded by 2, while conjugation is an isometry.
The reciprocal of a function with a genuine positive pointwise lower bound
has the genuine Hölder modulus obtained from the inverse-difference identity.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ComplexConjugate
namespace Euler2D
variable {X : Type*} [MetricSpace X]
-- Canonical inherited structures, named to short-circuit higher operator-space inference.
instance (priority := 2000) complexHolderSpace_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (HolderFunctionSpace X ℂ γ) :=
  Submodule.normedAddCommGroup (holderGraphSubmodule X ℂ γ)
instance (priority := 2000) complexHolderSpace_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (HolderFunctionSpace X ℂ γ) :=
  Submodule.normedSpace (holderGraphSubmodule X ℂ γ)
private lemma holderWith_of_norm_sub_bound {γ C : ℝ≥0} {f : X → ℂ}
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) : HolderWith C γ f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using h x y
  exact_mod_cast hb
namespace HolderFunctionSpace
variable {γ : ℝ≥0}
lemma norm_le_of_pointwise_holder_bounds (f : HolderFunctionSpace X ℂ γ) {C : ℝ≥0}
    (hsup : ∀ x, ‖f x‖ ≤ C) (hholder : HolderWith C γ (fun x => f x)) : ‖f‖ ≤ C := by
  rw [norm_eq_max_uniform_holder]
  apply max_le
  · exact (BoundedContinuousFunction.norm_le C.coe_nonneg).mpr hsup
  · exact_mod_cast hholder.nnholderNorm_le
lemma holderWith_pointwiseMul (f g : HolderFunctionSpace X ℂ γ) :
    HolderWith (2 * ‖f‖₊ * ‖g‖₊) γ (fun x => f x * g x) := by
  apply holderWith_of_norm_sub_bound
  intro x y
  change ‖f x * g x - f y * g y‖ ≤ (2 * ‖f‖ * ‖g‖) * dist x y ^ (γ : ℝ)
  have heq : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
  calc
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [heq]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ ‖f‖ * (‖g‖ * dist x y ^ (γ : ℝ)) +
        (‖f‖ * dist x y ^ (γ : ℝ)) * ‖g‖ :=
      add_le_add
        (mul_le_mul (norm_eval_le f x) (norm_sub_le_holder g x y) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_sub_le_holder f x y) (norm_eval_le g y) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)))
    _ = _ := by ring
/-- The literal pointwise product in the actual Hölder space. -/
def pointwiseMul (f g : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  ofMemHolder (toBCF γ f * toBCF γ g) (holderWith_pointwiseMul f g).memHolder
@[simp] theorem pointwiseMul_apply (f g : HolderFunctionSpace X ℂ γ) (x : X) :
    pointwiseMul f g x = f x * g x := rfl
theorem norm_pointwiseMul_le (f g : HolderFunctionSpace X ℂ γ) :
    ‖pointwiseMul f g‖ ≤ 2 * ‖f‖ * ‖g‖ := by
  apply norm_le_of_pointwise_holder_bounds (C := 2 * ‖f‖₊ * ‖g‖₊)
  · intro x
    rw [pointwiseMul_apply, norm_mul]
    have hm := mul_le_mul (norm_eval_le f x) (norm_eval_le g x) (norm_nonneg _) (norm_nonneg _)
    change ‖f x‖ * ‖g x‖ ≤ 2 * ‖f‖ * ‖g‖
    nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg g)]
  · exact holderWith_pointwiseMul f g
end HolderFunctionSpace
end Euler2D
end
