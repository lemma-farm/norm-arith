module
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi
noncomputable section
def faceCoordinateMeasures {d : ℕ} (τ : ℝ) (i : Fin d)
    (positive : Bool) : Fin d → Measure ℝ := fun j =>
  if j = i then Measure.dirac (if positive then τ / 2 else -τ / 2)
  else volume.restrict (Set.Ioo (-τ / 2) (τ / 2))
end
end CoarseDeGiorgi
