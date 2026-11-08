-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Classical.GalerkinGenerator
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Continuity and time integrability of the smooth forcing in each Fourier Galerkin system. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

local instance classicalForcingMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalForcingMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalForcingProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalForcingProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

                                                      
                                                      

                                                          
                                                       
                                                                                
                                                                                    
                                                                                  
                                    
                                                                        
                                                                 

                                                  
                       
                                                    
                                      
                                                                
                                                                
                                      
                                                                     
                                                                            
              
                                                                          
                                                                    
                                                          
                                        
       
          
                                        

                                                                                                
                                        
                                                            
                                                      
                                                                            
                                                         

                                                                         
                               
                                                
                                          
                                               
                                                
                                                       
                                                                
                                                                
                                                                          
                                             
                       
                                           
                                                         
                 
                                                                               
                                   
                                           
                                                                  
                                                        
            
              
       
                                                                           
                                                                              

                                                                                               
            
                                                                           
                                                    
                                      
                                                       
                                                               
                                                
                                                                  
                                                       
                                                                      
                                                              
                                                          
                                          
                    
                              
                                                                                        
                                                      
                                             
                                       
                                                                  
                                          
                                                                               
                                                   
                                                            
                 
                                                     
                                                            
                                                     
                                           
                                                                              
                                                      
                                                 
                                              
                                                                 
                                                                           
            
                     
         
       
                                                                     
           
                                          

                                                               
                       
                                                    
                                      
                                                                       
                                                               
                                              

end AVenhance.Infra.Classical

end
