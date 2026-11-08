module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6fc61adf0c98.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
import Mathlib.Analysis.Normed.Operator.Bilinear
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
