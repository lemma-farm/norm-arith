/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsCylinder

/-!
# Uniform polynomial moments of a white-noise field

Let `ψ` be a random field such that every value `ψ(·, y)` is almost surely `W h_y` with `h_y ∈ L²`,
and `E ψ(y)² ≤ V` for all `y`. Then all moments of `ψ(y)` are bounded uniformly in `y`
(`exists_integral_field_pow_le`), and so are the moments of `Q(ψ(y))` for a polynomial `Q`
(`exists_integral_polyField_sq_mul_sq_le`).
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

                                                                     
                                                               
                                                                                
                                                            
                                                           
                                                   
                                                                                 
                       
                                                    
                                      
                                                     
         
                                                                  
                                 
                                  
                                                 
                                                                      
            
                                   
                    
            

                                                                               
                                                                         
                                       

variable {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ψ : Ω → SpaceTime → ℝ}

                                                  
                                                            
                                                                                    
                                                            
                                                           
                                       
                                                                                  
                                         
                              
                                                
                                                                  
                                          
                                                                                                   
                                            
                 
                           
                                                                 
                                                                       
                            
                                                                        
                                                                    
           
                                                      
             
                                                                                                    

                                                                                                  
                                
                                     
                                             
            
                                                      
            

                                                                         
                                                                     
                                                                                    
                                                                            
                        
                                                                
                                            
                                 
                                                             
                                                                                           
                              
                                                                                    
           
                                                                
                                              
                                                    
                                                                                       
                  
                                                                             
                                                                 
                                                           
                                                           
                                          
                                                                                  
                 
                
                                                     
                                                     
                                       
                                                   
                                
                                           
                                                                                    
                                                         
                                                          
                                                      
                                                                                                     
       
                                                        
               
                                                                                              
                                                                                         
                                                      
                                                                                       
                                   
                                                           
                                                       
                                               
                           

                                                                                               
                    
                                                                      
                                                                                    
                                                                            
                            
                                                                                                   
                                                                     
                                                                           
                                                                           
                                                                 
                                                                                            
                                       
                                                                            
                                         
                                                                                   
                                                             
                                                           
                                                                                      
                                                                                             
                                                          
                    
                   
                                                                         
                                                
                                                                                 
                                                         
                                                         
                            

end RegularityStructures

end
