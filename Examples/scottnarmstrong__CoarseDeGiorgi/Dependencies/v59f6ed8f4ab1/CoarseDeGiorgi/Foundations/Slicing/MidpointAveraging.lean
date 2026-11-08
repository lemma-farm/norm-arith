module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Foundations.FracGeometry.TranslationEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Midpoint averaging with constants depending only on dimension. -/
@[expose] public section
namespace CoarseDeGiorgi.Foundations.Slicing
open Homogenization MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
/-- Open Euclidean ball on the coordinate carrier. -/
def euclidBall {d : ℕ} (x : Vec d) (R : ℝ) : Set (Vec d) :=
  {z | Euclid.eDist2 x z < R}
/-- The power of the difference appearing in both fractional kernels. -/
def differencePower {d : ℕ} (r : ℝ) (F : Vec d → ℝ) (x z : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|F x - F z| ^ r)
theorem measurableSet_euclidBall {d : ℕ} (x : Vec d) (R : ℝ) :
    MeasurableSet (euclidBall x R) :=
  measurableSet_lt (Euclid.continuous_eDist2.measurable.comp
    (measurable_const.prodMk measurable_id)) measurable_const
end
end CoarseDeGiorgi.Foundations.Slicing
