/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Duhamel
import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Spatial derivatives commute with the heat operator and the Duhamel integral

If `g ∈ C(T³, E)` has a continuous derivative `Dg` (on the periodic lift), then so does
`P_t g`, with derivative `P_t Dg`. If every `h(s)` has derivative `Dh(s)` and `Dh` is a continuous
path, then the Duhamel integral `∫₀ᵗ P_{t-s} h(s) ds` has derivative `∫₀ᵗ P_{t-s} Dh(s) ds`.
Both are differentiation under the integral sign with the derivative falling on the data.
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped Interval

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                                                
                                                                                             
                                                                                      
         
                            
                                                
                                                                           
                                                                            
              
                                                                             
                                                            
                                                                                 
                                          
                                         
                                                                               
                                                                           
                                                                               
                                                                                                    
                
                                       
                                                                                     
             
                                                                                      
                                                                                        
                                                         
                                                                                            
                               
                                                                                 
                                                                             
                                                                                          
                                                                       
                                                
                                                                  
                                                                              
                                                                          
                                

variable [CompleteSpace E]

                                                               
                                                  
                                                                                    
                                                                  
                                                      
                                                    
         
                                                     
                                                                            
             
                              
                             
                                                                                           
                                                         
                                                                                                 
                                                                          
                                              
                                                                                                  
                                                                                   
                                                                            
                                                                            
                                                                                      
             
                                                                             
                                                                             
                                                                 
                                                            
                                     
                                                                                              
                                                                       
                                                                          
                                                                         
                                                                                  
                                                                              
                                                                         
                                                                 
                                                                    
                                                   
                            
                                                                         
                                                                                
                                                                    
                                                                      

end RegularityStructures.PDE

end
