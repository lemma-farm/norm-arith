-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.Step3.LocalizedEquationTested
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.Step3.DuhamelAdjoint
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.Step3.LocalizedEquationDuhamelKernels
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
private lemma parabolic_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume := by
  have h := (measurePreserving_add_right (volume : Measure Vec3) (-y.1)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-y.2))
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving (fun x : Vec3 × ℝ =>
    (x.1 + -y.1, x.2 + -y.2)) (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl
end CKN.Core.Step3
