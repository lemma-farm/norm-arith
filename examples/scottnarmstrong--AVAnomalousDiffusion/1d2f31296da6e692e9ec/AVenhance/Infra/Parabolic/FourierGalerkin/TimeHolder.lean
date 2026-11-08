-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The time Cauchy estimate

An `L²`-in-time energy bound gives the square-root modulus needed by weak path compactness. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance two_ne_top_timeHolder : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

                                                                                             
                                                    
                                                                      
                                           
                                                      
                                                                 
                                             
                                                            
                                                       
                                                  
                                                                
                                                                  
                                                   
                                                                             
                                                      
                                                              
                                               
                                                        
                                                                   
                                                      
                                           
        
                                             
                                                          
                                            
                 
                                                        
                       
                                                                             
                                                 
                 
                       
                                             
                                                             
                                                                    
                             
                                           
                             
                                                               
                                                 
             
                             
                           
                                     
                                 
                                                        
                                             
        
                                                 
                  
                     
                                               
                                                     
                                                                   
        
                                 
                               
                             
                
                                  
                           
                                                                   
                            
                                                             
                    
                       
                                                               
                                                                             
                                                           
                                            
                
      
                                                                                    
                                          
                                                    

end AVenhance.Infra.Parabolic.FourierGalerkin

end
