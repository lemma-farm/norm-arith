module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.EuclidDist
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi
noncomputable section
def fracKernelWithDimension {d : ℕ} (dimension α r : ℝ) (w : Vec d → ℝ)
    (p : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (|w p.1 - w p.2| ^ r /
      euclidDist p.1 p.2 ^ (dimension + α * r))
end
end CoarseDeGiorgi
