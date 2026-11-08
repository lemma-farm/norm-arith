-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.LimitPassage
public import Mathlib
/-!
# Density of the real symmetric Fourier cutoffs

The union of the finite real Fourier synthesis ranges is dense in scalar torus `L²`.  This is the
test space used by the weak path compactness argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance densityMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance densityMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance densityProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance densityScalarTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
  inferInstance
local instance densityTwoNeTopFact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance densityOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

                                                                                        
              
                                                                   
                                            
                                                                                           

                                                        
                                            
                                                                         
                                   
                         
                                
           

                                                                                              
                          
                                                                     
                         
                                                                    
                          
                                                                         
                                                             
                                    
                                                
                               
                                       
                                                                
                                        
                                                               
                           
                              
                                                            
                                             
           
                                                                             
               
                                                             
                                           
                                                                    
                     
                                                                                
                                      
                                                          
                                                            
                                                                   
              
                                            
                                                
                                                          
      
                                  
                                                                                 
                                                        
                                                             
         
                                                                           
                                                                                

                                                                             
                                                           
                                                                                           
                 
                                                             
                                                
                
                                                  
                                                        
                         
                                                  
                   
                                                                             
                                       
                 
                       
                                                                        

                                                                   
                                          
                                             

                                                                                     
                                                           
                       
              
                                               
                           
                                                                                    
                                                
                                     
                       
                                                                                 
                                                  
                                                  

end AVenhance.Infra.Parabolic.FourierGalerkin

end
