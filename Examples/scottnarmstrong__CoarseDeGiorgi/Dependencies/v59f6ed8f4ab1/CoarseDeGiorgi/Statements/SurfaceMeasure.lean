module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.CubeFaceMeasure
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.Homogenization.Ambient.CoefficientField
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
def surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) := by
  classical
  exact ∑ i : Fin d, ∑ positive : Bool, cubeFaceMeasure τ i positive
end
end CoarseDeGiorgi
