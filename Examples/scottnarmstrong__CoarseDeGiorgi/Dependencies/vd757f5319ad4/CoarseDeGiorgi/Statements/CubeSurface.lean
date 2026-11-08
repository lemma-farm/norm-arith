module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.Homogenization.Ambient.CoefficientField
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
def cubeSurface {d : ℕ} (τ : ℝ) : Set (Vec d) :=
  {x | ‖x‖ = τ / 2}
end
end CoarseDeGiorgi
