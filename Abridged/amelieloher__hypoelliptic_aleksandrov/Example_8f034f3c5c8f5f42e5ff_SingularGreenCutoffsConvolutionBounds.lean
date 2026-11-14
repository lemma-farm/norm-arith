module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Prod

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v8f3676843394.HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # C² homogeneous functions and their continuous Bellman images -/
@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov
def bellmanDv (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ phi q (0, 1)
/-- The second velocity derivative. -/
def bellmanDvv (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ (bellmanDv phi) q (0, 1)
end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v8f3676843394.HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionContinuous ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The continuous zero extension of a positive-degree Bellman function -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology
/-- Extend the punctured homogeneous function by its forced value zero at the origin. -/
def bellmanOriginExtension (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  if q = (0, 0) then 0 else phi q
end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v8f3676843394.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Literal first and second parameter jets of position convolution -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology
/-- The scalar position projection used by the parameter jets. -/
def barrierPositionProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
/-- The scalar velocity projection used by the parameter jets. -/
def barrierVelocityProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
def barrierConvolutionSecondJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection).smulRight barrierPositionProjection +
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection).smulRight
      barrierVelocityProjection
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_8f034f3c5c8f5f42e5ff_SingularGreenCutoffsConvolutionBounds ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Transparent norm bounds for the position-convolution parameter jets -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

set_option linter.unusedVariables false in
theorem barrierConvolutionSecondJet_norm_le (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Autonomous_barrier_projection_norm_le : ∀ (a b : ℝ),
      ‖a • HypoellipticAleksandrov.KineticAleksandrov.Autonomous.barrierPositionProjection +
            b • HypoellipticAleksandrov.KineticAleksandrov.Autonomous.barrierVelocityProjection‖ ≤
        |a| + |b|)
    :
    ‖barrierConvolutionSecondJet κ phi q Y‖ ≤
      |deriv (deriv κ) (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        2 * |deriv κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| +
          |κ (q.1 - Y)| * |bellmanDvv phi (Y, q.2)| := by
  unfold barrierConvolutionSecondJet
  have h1 := h_HypoellipticAleksandrov_KineticAleksandrov_Autonomous_barrier_projection_norm_le
    (deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
  have h2 := h_HypoellipticAleksandrov_KineticAleksandrov_Autonomous_barrier_projection_norm_le
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
    (κ (q.1 - Y) * bellmanDvv phi (Y, q.2))
  have hh := norm_add_le
    ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection |>.smulRight barrierPositionProjection)
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection
        |>.smulRight barrierVelocityProjection)
  have hX : ‖barrierPositionProjection‖ = 1 := ContinuousLinearMap.norm_fst ℝ ℝ ℝ
  have hv : ‖barrierVelocityProjection‖ = 1 := ContinuousLinearMap.norm_snd ℝ ℝ ℝ
  simp only [ContinuousLinearMap.norm_smulRight_apply, hX, hv, mul_one] at hh
  simp only [abs_mul] at h1 h2
  linarith only [hh, h1, h2]
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
