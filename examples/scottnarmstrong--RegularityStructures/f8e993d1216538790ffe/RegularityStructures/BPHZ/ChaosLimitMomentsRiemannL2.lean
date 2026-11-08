/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemann
public import RegularityStructures.BPHZ.ChaosLimitMomentsField
                                                                      

/-!
# Uniform second moment of the sampled tested fields

For finitely-valued measurable sampling maps `π`, `E (chaosIntegral … π)²` is bounded by a constant
independent of `π` (`exists_integral_chaosIntegral_sq_le`). The proof applies the weighted
Cauchy-Schwarz bound `integral_sq_integral_mul_le` to the inner integral and then to the outer
integral, with the uniform moment bounds of `ChaosLimitMomentsField`.
-/

public section

open MeasureTheory

namespace RegularityStructures

universe u

                                                                                          
                                                                   
                                                        
                                            
                                                      

                                                                                                    
                                                                                             
                                                                                         
                                                             
                                                          
                                          
                                                             
                                                                
                                               
                                                     
                                                         
                               
                                                                               

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ψ : Ω → SpaceTime → ℝ}

                                                                                    
                                                                   
                                                                                    
                                                                            
                                                         
                                                                                    
                                                                                              
                                                            
                                                                                 
                                                            
                                 
                                                                                         
                            
                                                                            
                                                                 
                                                                            
                                                                          
                                                 
                                     
                                                                    
                                   
                                                                 
                                                                                                
                                   
                                                                              
                                                                                            
                                                   
                                                                          
                                                              
                                                                                              
                                                                                       
           
                                                                                              
                                                                              
                                       
                                                       
                                                               
                                                                   
                                                                   
                                                                            
                                                                    
                       
                               
                                                                            
                        
             
                                          
                                                                                
                                                                                         
                                                                
                                                   
                                                                                 
                                                                           
                                     
                                                               
                                                  
                                              
                                                                
           
                                                                                
                                                                                
                                                                                
                                                              
                                                           
                  
                                                                                   
                       
                                                                           
                                               
                                                     
                                                                                                
                                                                                    
                                                        
                                                       
                          
                                                                            
                                 
                                                                
                                                                             
                                                                                             
                                              
                                                          
                      
                                                       
                                                                                             
                                              
                                                                                      
                          
                                                                           
                                                     
                                                                            
                                                 
                  
                        
                             
                
                
                                                                                 
                                                          
                                                                                   
                                       
                                                                               
             
             

end RegularityStructures

end
