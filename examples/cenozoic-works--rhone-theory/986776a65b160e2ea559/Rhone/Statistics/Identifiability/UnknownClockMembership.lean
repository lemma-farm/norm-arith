/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockReparameterization
public import Rhone.Statistics.Identifiability.PanMembership
public import Mathlib
/-! # Membership against every continuous proper panmictic size history -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

structure ProperPanModel where
  rate : ℝ → ℝ
  clock : ℝ → ℝ
  rate_continuous : Continuous rate
  clock_continuous : Continuous clock
  rate_nonneg : ∀ t, 0 ≤ t → 0 ≤ rate t
  clock_derivative : ∀ t, 0 ≤ t → HasDerivAt clock (rate t) t
  clock_diverges : Tendsto clock atTop atTop
  pre : PanPreModel rate

                                                                                                

                                                                                           
                                                                                  
                                       

                                                         
                                                               
                                                                              
                                       

                                                                                    
                                                                                
                                      
                                                                    
                                        
                                                                         
                                                                             
                                                                        

                                                                   
                                              
                                                                                         
                                                                    
                                  
                               
                                                    
                                                    
                                                   
                                   
                                                                                         
                                                              
                                         
                                          
                                          
                                                    
                                                                                
                                           
             
                 
                                                                                     
                                       
                                                                         
                                                              
                                                                               
               
                                           
                                                        
            
            
                              
                             
                    
                  
                             
                              
                                                                 
                                  
                               
                  
                 
            

end Rhone.Statistics.Identifiability
