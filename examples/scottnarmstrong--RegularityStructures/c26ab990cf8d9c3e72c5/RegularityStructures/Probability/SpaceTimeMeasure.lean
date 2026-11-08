/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Translation invariance of the measure on space-time

The measure on `ℝ × T³` is the product of Lebesgue measure and the Haar measure of the torus.
Mathlib does not find the product Haar instances for `volume` on a product type by itself, so we
record them here:

* `volume` on `SpaceTime` is an additive Haar measure (hence translation invariant);
* it is invariant under `z ↦ -z`.

Consequently `w ↦ z - w` preserves `volume`, which gives the change of variables
`∫ f (z - w) dw = ∫ f` and the transfer of `Lᵖ` membership.
-/

public section

open MeasureTheory

namespace RegularityStructures

instance isAddHaarMeasure_volume_spaceTime : (volume : Measure SpaceTime).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

instance isNegInvariant_volume_spaceTime : (volume : Measure SpaceTime).IsNegInvariant := by
  have : (volume : Measure Torus3).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  exact ⟨((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure Torus3))).map_eq⟩

/-- Reflection through a point, `w ↦ z - w`, preserves the measure on space-time. -/
theorem measurePreserving_sub_left_spaceTime (z : SpaceTime) :
    MeasurePreserving (fun w : SpaceTime => z - w) volume volume :=
  Measure.measurePreserving_sub_left _ z

                                                     
                                                                                             
                                         
                                
                                      

                                                     
                                                                                             
                                         
                                
                               

                                                                                            
                                                    
                                   
                                                                    

                                                                             
                                                             
                                      
                                                                           

end RegularityStructures

end
