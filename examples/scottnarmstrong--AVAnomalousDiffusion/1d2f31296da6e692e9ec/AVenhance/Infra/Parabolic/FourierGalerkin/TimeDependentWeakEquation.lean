-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakLimitPassage
public import AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import Mathlib
/-!
# Weak equation for time-dependent finite Fourier tests

The separated Fourier-mode identities sum to the weak equation for the spatial Fourier cutoff of
an arbitrary smooth periodic spacetime test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance timeWeakEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeWeakEquationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeWeakEquationProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

                                                                    
                                      
                                                                                 
                                     

                                                                   
                                        
                                                                                       
                                 
                                   

                                                                     
                                        
                                                                                             
                                   
                                   

                                                                           
                                  
                                                    
                                                               
                                                                         
                                                  

                                                                                              
                                              
                                                                             
                                                            
                                                                 
                                                                               
                            
                                                                                 
                            
                       
                                                               
                                                    
                                             
             
                                         
                     
                              
                                                           
                                   
                                      
                                                                                               
                                          
                     
                                       
                                                     
                                            
                                      
                                                                                   
                                                
                     
                                
                                                   
                                       
                                      
                                                                                   
                                         
                                                 
                                                                
           
                                                 
                                                  
                                                                    
                                                       
                                                 
                                          
                                               
                                                      
                                                  
                                                         
                                                                          
                                                 
                    
                                                                                      
                     
                                                                                
                        
                           
                                                                               
                                                                      
                                                                       
                                                   
                                                               
                                                             
                                                                                                                                
                   
             
                                          
                                                          
                                                     
                                                             
                                                         
                                                          
                                                      
                                         
                                                                      
                              
              
                 
                                                                           
                                 

end AVenhance.Infra.Parabolic.FourierGalerkin

end
