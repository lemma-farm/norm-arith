module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Foundations.FracGeometry.TranslationEnergy
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
variable {n : ℕ}
/-- Place the slicing coordinate first and the tangential coordinates afterwards. -/
def flatJoin (l : ℝ) (x : Vec n) : Vec (n + 1) := Fin.cons l x
theorem volume_preserving_flatJoin :
    MeasurePreserving (fun lx : ℝ × Vec n => flatJoin lx.1 lx.2)
      (volume.prod volume) volume := by
  convert (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm using 1
  ext lx i
  simp [flatJoin, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
end
end CoarseDeGiorgi.Foundations.FracGeometry
