module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Statements.FracKernel
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Measure.Prod
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
def fracSeminorm {d : ℕ} (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d, fracKernel α r w p
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)
end
end CoarseDeGiorgi
