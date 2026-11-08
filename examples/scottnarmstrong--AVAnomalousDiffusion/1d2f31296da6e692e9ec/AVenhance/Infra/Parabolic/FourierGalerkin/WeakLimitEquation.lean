-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProduct
public import AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting
public import AVenhance.Infra.Parabolic.FourierGalerkin.FiniteWeakForm
public import AVenhance.Infra.Parabolic.FourierGalerkin.LimitConstruction
public import Mathlib
/-!
# Product-space weak equation on finite Fourier tests

This module connects the finite Galerkin identities to the synchronized product-space limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

local instance weakLimitEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakLimitEquationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakLimitEquationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

                                                                                            
                                    
                                                                                     
                                                 
                                                         
                                                
                                                 
                                                        
                                          
                                   
                                                                 
                                                        
                                                     
                                                                  
                                                                      
                                    
                                                                               
                                             
                                                                                  
                                                             
                                          
                           
                                               
                
                   
                                            
                                   
                         

end AVenhance.Infra.Parabolic.FourierGalerkin

end
