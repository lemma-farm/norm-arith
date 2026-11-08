module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6fc61adf0c98.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets
import Mathlib.Analysis.Normed.Operator.Prod
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
