module

/-
Good and bad degrees for the two possible pairings of two independent coordinates.
-/
public import GraphMarkovMatching.Potential.Degrees
public import GraphMarkovMatching.Potential.Inverse
public import GraphMarkovMatching.Support.Contraction

@[expose] public section

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

                                                                    
                                             
                                                   
                                                               
                                                                                  
                                                       
                                    
                            
                                                                                     
                                                       
                                                                                      
                                                                                    
                                        
                                                                                      
                                                       
                                                         
                                                                  
                                                                    
                                       
                                                                        
                                                    
                                                                              
                                     
                                        
                                                            
                                                                               
                                                                               
                                                               
                                           
                                                                              
                                     
                                        
                                                            
                                                                               
                                                                               
                                                             
                                            
                                                                      
                                                                    
        
                                                                                   
                        
                                                                                         
                                                                          
                                                                                  
                                               
                                 
                                                           
                                                             
                                          
                                
            

                                                                    
                                             
                                                         
                                                         
                                                     
                                                                                 
                                    
                            
                                                             
                                                                  
                                                                    
                                                                    
                                                                          
           
                                         
                                         
                           
                                                                       
                                                                             
                    
                                                                                
                              
                                                          
                                                          
                                                          
                                                          
                                    
                                           
                                    
                                         
                                              
                                           
                                    
                                         
                                              
                                           
                                         
                                              
                                           
                                              
                                                                                  
                                     
                                        
                                                                
                                                                                   
                                                                               
                                                               
                                              
                                                                                        
                                                                                  
                                     
                                        
                                                                
                                                                                   
                                                                               
                                                               
                                              
                                                                                        
                                                                                  
                                 
                                                                                          
                                        
                                                                
                                                                    
                                                                               
                                                                                           
                            
                                                                                  
                                 
                                                                                          
                                        
                                                                
                                                                    
                                                                               
                                                                                           
                            
         
                                                                            
                     
                                                                   
                                                                      
                                                                      
                                                                          
                                   
                                                                              
                                                                                  
                                                                                  
                                                                                        
                                                                 
                                                         
                                                           
                           

                                                                           
                                                      
                                                                     
                                                 
                                                         
                                       
                               
                                  
                                                                                     
                                                               
                                               
                                                                    
         

                                                                           
                                                      
                                                 
                                                   
                                                                           
                                       
                                                  
                                                   
                                                               
                                                          
                                                  
                                                                            
                                 
                                          
                                                
                                                                              
                                   
                                                                
                                   
                                         
                                                    
             

lemma ennreal_two_mul_le_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ⊤
  · by_cases hb : b = 0
    · simp [ha, hb]
    · have : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
      rw [ha]
      calc 2 * (⊤ * b) ≤ ⊤ := le_top
        _ ≤ ⊤ ^ 2 + b ^ 2 := by simp
  · by_cases hb : b = ⊤
    · by_cases ha0 : a = 0
      · simp [hb, ha0]
      · rw [hb]
        calc 2 * (a * ⊤) ≤ ⊤ := le_top
          _ ≤ a ^ 2 + ⊤ ^ 2 := by simp
    · have h2 : (2 : ℝ) * (a.toReal * b.toReal) ≤ a.toReal ^ 2 + b.toReal ^ 2 := by
        nlinarith [sq_nonneg (a.toReal - b.toReal)]
      calc 2 * (a * b)
          = ENNReal.ofReal (2 * (a.toReal * b.toReal)) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb, ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal (a.toReal ^ 2 + b.toReal ^ 2) := ENNReal.ofReal_le_ofReal h2
        _ = a ^ 2 + b ^ 2 := by
            rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
              ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]

                                                                            
                                                                             
                                                                              
                                     
                                        
                                                            
                                                                               
                                                                               
                                                               
                                           
                                                          
                                                                                   
                                     
                                         
                                  
                                                                               
                                      

section
variable {X : Type}

                                                                            
                           
                                                       
                                                     
                                                          
                                                      
                                       
                                         
                                                   
                                                        
                                              
                      
                      
                      

                                                                           
                           
                                                       
                                                     
                                                          
                                                      
                                       
                                         
                                                   
                                                        
                                              
                      
                      
                      

                                                                            
                                                   
                                                                     
             
            
                                                                          
                
                                                                             
                   
                                                        
                                                                 
                                                    
                                                     
                                                                      
                                            
                                                                    
                                 

                                                                   
                 
                                                   
                                        
                                            
                                          
                                                  
                                                      
       

                                                                  
                                  
                                                 
                                                     
                                                       
                                                                      
                                                
                                                          
                                                               
                                   
                                                                     
                                           
                                       
                                               
                                                    
                                              

                                                                          
                                  
                                                 
                                                     
                                                       
                                                                      
                                                
                                                          
                                                               
                                   
                                                                     
                                           
                                       
                                              
                                                    
                                              

end

end GraphMarkovMatching
