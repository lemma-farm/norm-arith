-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.GradientSpace
public import AVenhance.Statements.Roots.UnitCube
public import Mathlib

/-!
# Transfer of initial data to the unit torus

The datum is only assumed square-integrable on the open unit cube and need not be
periodic. This module transports that representative to the quotient torus through its canonical
`Ioc` representative, using the fact that the open and half-open cells agree almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

local instance frozenInitialMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenInitialMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenInitialProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

                                                                                        
                                                      
                                           
                                                                                     
                                                            
                                           
                                                        
                                                           
                                                                  
                                  
                                                      
                                                                        
                            
                                            
                                          
                                                    
                                                                            
                                                                  
                                        
                                                                            
                                                
                                                                          
                                                                            
                                                                                           
                                                                           
                                                                                         
                                                           
                                                                            
                                                                                               
                                                                               
                                                              
                                                 
                                                    
            
       
                    

end AVenhance.Infra.Parabolic.FourierGalerkin

end
