module

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
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Prod

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6fc61adf0c98.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets ====
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
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_0043544762b63224b9b5_SingularGreenCutoffsConvolutionBounds ====
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
/-- A scalar combination of the two coordinate projections has its elementary norm bound. -/
theorem barrier_projection_norm_le (a b : ℝ) :
    ‖a • barrierPositionProjection + b • barrierVelocityProjection‖ ≤ |a| + |b| := by
  exact (norm_add_le _ _).trans_eq (by
    simp only [norm_smul, Real.norm_eq_abs, barrierPositionProjection,
      barrierVelocityProjection, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd,
      mul_one])
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
