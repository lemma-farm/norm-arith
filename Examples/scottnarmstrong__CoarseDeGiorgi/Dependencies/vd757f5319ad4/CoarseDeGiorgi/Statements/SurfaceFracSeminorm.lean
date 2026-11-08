module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Statements.FracKernelWithDimension
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Statements.SurfaceMeasure
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
def surfaceFracSeminorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d, fracKernelWithDimension ((d : ℝ) - 1) α r f p
    ∂((surfaceMeasure τ).prod (surfaceMeasure τ))).rpow (1 / r)
end
end CoarseDeGiorgi
