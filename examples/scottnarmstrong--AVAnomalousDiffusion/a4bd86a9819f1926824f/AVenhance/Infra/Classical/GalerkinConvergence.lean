-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Classical.GalerkinExistence
public import AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting
public import Mathlib
/-! Nested-cutoff coefficient maps for the classical Galerkin sequence. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin

local instance classicalConvergenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalConvergenceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

                                                                                          
                                                                 
                                                 
                                            
                                                            

       
                                                                           
                                               
                                        
                                                   
                                              

end AVenhance.Infra.Classical

end
