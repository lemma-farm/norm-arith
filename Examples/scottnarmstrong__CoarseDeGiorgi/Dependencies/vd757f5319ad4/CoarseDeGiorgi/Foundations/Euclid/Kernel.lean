module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Foundations.Euclid.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace CoarseDeGiorgi.Foundations.Euclid
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ}
/-- The same integrand using Euclidean distance. -/
def euclidKernel (β r : ℝ) (w : Vec d → ℝ) (xy : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|w xy.1 - w xy.2| ^ r / eDist2 xy.1 xy.2 ^ β)
end
end CoarseDeGiorgi.Foundations.Euclid
