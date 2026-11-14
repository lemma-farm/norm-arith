module

public import Mathlib
public import Mathlib.Topology.MetricSpace.HolderNorm

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_bd4e17412fbbf257b5ec_ContourHolderSpace ====
/-!
# The actual Hölder Banach space for contour functions

A function is stored together with its genuine off-diagonal difference
quotient.  The equations defining that quotient are kernels of actual
continuous linear maps.  Their closed intersection is therefore complete
in the inherited product norm.  The first component is the function itself;
the second component is uniquely determined and bounds its Hölder modulus.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Euler2D
variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The actual pairs of distinct domain points. -/
abbrev HolderDifferencePair := {p : X × X // p.1 ≠ p.2}
abbrev HolderGraphAmbient := (X →ᵇ E) × (HolderDifferencePair X →ᵇ E)
/-- A difference-quotient equation at a fixed actual pair of distinct points. -/
def holderGraphOperator (γ : ℝ≥0) (p : HolderDifferencePair X) :
    HolderGraphAmbient X E →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp
      (ContinuousLinearMap.snd ℝ (X →ᵇ E) (HolderDifferencePair X →ᵇ E)) -
    (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ •
      (((BoundedContinuousFunction.evalCLM ℝ p.val.1 : (X →ᵇ E) →L[ℝ] E) -
          BoundedContinuousFunction.evalCLM ℝ p.val.2).comp
        (ContinuousLinearMap.fst ℝ (X →ᵇ E) (HolderDifferencePair X →ᵇ E)))
/-- The actual closed graph of all off-diagonal Hölder difference quotients. -/
def holderGraphSubmodule (γ : ℝ≥0) : Submodule ℝ (HolderGraphAmbient X E) :=
  ⨅ p : HolderDifferencePair X, (holderGraphOperator X E γ p).ker

/-- Genuine bounded Hölder functions, with their uniquely determined
difference quotient and the inherited complete norm. -/
abbrev HolderFunctionSpace (γ : ℝ≥0) := holderGraphSubmodule X E γ

variable {X E}

instance holderFunctionSpace_coeFun (γ : ℝ≥0) :
    CoeFun (HolderFunctionSpace X E γ) (fun _ => X → E) :=
  ⟨fun f => f.val.1⟩
namespace HolderFunctionSpace
variable (γ : ℝ≥0)

variable {γ}


set_option linter.unusedVariables false in
/-- The actual uniform Hölder estimate encoded by the graph, using the
genuine metric distance on the domain. -/
theorem norm_sub_le_holder (f : HolderFunctionSpace X E γ) (x y : X) 
    (h_Euler2D_holderFunctionSpace_quotient_eq : ∀ {X : Type u_1} {E : Type u_2} [inst : MetricSpace X] [inst_1 : NormedAddCommGroup E]
      [inst_2 : NormedSpace ℝ E] {γ : NNReal} (f : ↥(Euler2D.HolderFunctionSpace X E γ))
      (p : Euler2D.HolderDifferencePair X),
      ((↑f : Euler2D.HolderGraphAmbient X E).2 : Euler2D.HolderDifferencePair X → E) p =
        (Dist.dist (↑p : X × X).1 (↑p : X × X).2 ^ (↑γ : ℝ))⁻¹ •
          (((↑f : Euler2D.HolderGraphAmbient X E).1 : X → E) (↑p : X × X).1 -
            ((↑f : Euler2D.HolderGraphAmbient X E).1 : X → E) (↑p : X × X).2))
    (h_Euler2D_HolderFunctionSpace_norm_quotient_le : ∀ {X : Type u_1} {E : Type u_2} [inst : MetricSpace X] [inst_1 : NormedAddCommGroup E]
      [inst_2 : NormedSpace ℝ E] {γ : NNReal} (f : ↥(Euler2D.HolderFunctionSpace X E γ)),
      ‖(↑f : Euler2D.HolderGraphAmbient X E).2‖ ≤ ‖f‖)
    :
    ‖f x - f y‖ ≤ ‖f‖ * dist x y ^ (γ : ℝ) := by
  by_cases hxy : x = y
  · simp only [hxy, sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)
  let p : HolderDifferencePair X := ⟨(x, y), hxy⟩
  have hpow : 0 < dist x y ^ (γ : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hq : ‖f.val.2 p‖ ≤ ‖f‖ :=
    (f.val.2.norm_coe_le_norm p).trans (h_Euler2D_HolderFunctionSpace_norm_quotient_le f)
  rw [h_Euler2D_holderFunctionSpace_quotient_eq] at hq
  change ‖(dist x y ^ (γ : ℝ))⁻¹ • (f x - f y)‖ ≤ ‖f‖ at hq
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpow] at hq
  apply (div_le_iff₀ hpow).mp
  simpa only [div_eq_mul_inv, mul_comm] using hq

end HolderFunctionSpace

end Euler2D
end
