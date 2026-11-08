import Mathlib

/-!
# Finite-dimensional real `ell_p` geometry for the frozen O3 probe

The exponent is a genuine real number and the dimension is an arbitrary natural
number.  We use the literal finite-sum formula from the TeX source rather than
the ambient Euclidean norm on `Fin d → ℝ`.
-/

open scoped BigOperators

namespace O3

/-- A point of the arbitrary finite-dimensional ambient space `ℝ^d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- The coordinate pairing used between `ell_p` and `ell_q`. -/
def pairing {d : ℕ} (x y : Point d) : ℝ := ∑ i, x i * y i

/-- The real conjugate exponent `q = p / (p - 1)`. -/
noncomputable def conjugateExponent (p : ℝ) : ℝ := Real.conjExponent p

                                                                               

                                                                
                                                 
                                            

                                                       
                                 
                                                      

                                                                           
noncomputable def lpPower (p : ℝ) {d : ℕ} (x : Point d) : ℝ := ∑ i, |x i| ^ p

/-- The literal finite-dimensional `ell_p` norm for a real exponent. -/
noncomputable def lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := (lpPower p x) ^ (1 / p)

                                                                            
                                                                         

                                                                          
                                                     

                                                           
                                     
                    

                                                          
                                    
                       

                                                            
                                        
           
                               
               
            
            
                
                   
                       
                                                                       
                                            
                                                                          

                                                           
                                       
                                                                

                                                                       
                                
             
           
                
                                          
              
                        

                                                           
                                      
                

                                                          
                                    
               

                                                                              
                               

                                                          
                                       
                

                                                           
                                       
                

                                                                                   
                                                                   
                             
                                               
                                        
                                                                    

                                                        
                                                                       
                             
                                                 
             
             
                                              
                                            
                                                        
                                                          
                                                       
            
                                       

                                                                              
                                                                            
                               

                                                                         
                                                                           
                             

                                                                        
                                                                       
                          
                                                               

                                    
                                                                             
                                            

                                                                         
                                                                             
                       
                                                      
                                                 
                              
                                                                              
                                                  

                                                                             
                                                                            
                                                  
                                                       
                                
                                                                     
                                                    

end O3
