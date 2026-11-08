-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ScalarRepresentative
public import AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProduct
public import Mathlib
/-!
# Integrability of the drift pairing at the synchronized limit
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped ENNReal RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance solutionIntegrabilityMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance solutionIntegrabilityProbabilityCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance solutionIntegrabilityProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

                                                                                                        
                                                                              

                                                                                  
                                                           
                                                                  

                                                                                   
                        
                                                                     
                                                          
                                                                          
                                                               
                                                                       
                                                               
                                      
                                                                          
                                                           
                                
                                                                       
                                                            
                                     
                                                                                              
                                                 
                                                        
                                                                     
                                               
                                
                                                                      
           
                                                               
                          

                                                                                        
                                                                       
                                                          
                                    
                                         
                                                       
                                                
                                                               
                             
                                                                                        
                                             
                                                             
                                           
                                                         
                           
                                    
                             
                                                                            
                                  
                                         
                                                           
                                             
                                                                                              
                                                        
                           
                                                             
                                                              
                               
                                                
                                                                      
             
                                         
                                                                                        
                                                                 
                                                                     
                                                         
                                                                                                              
                                                                       
                                              
        
                                

end AVenhance.Infra.Parabolic.FourierGalerkin

end
