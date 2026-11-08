module

public import Mathlib
public import LeanLab.VanDerCorput1939.Global

/-!
P0067 van der Corput 1939, the constant K = ∏_p (1 + 1/(p − 1)³) of the ternary singular series.
Numeric bounds 2.29 < K < 2.33, from the factors at p = 2, 3, 5, 7 and the tail
Σ_{n ≥ 11} 1/(n − 1)³ ≤ 1/90. A float computation over the primes below 10^6 gives
K ≈ 2.30096, inside the proved range.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.VanDerCorput1939
open Real Finset

attribute [local instance] Classical.propDecidable

                        
                                                             

                                        
                                                                          

                                                                              
                                                   
                                             
            

                                                               
                                                     

                                          
           
                   
                         
                                           
                                                     
            
                

                                                           
                                                                                 
           
                   
                                                             
                              
                

                                       
                                                                                      
                                                                 
                                 
                                                      
                                                   

                              
                                                  
                                                                        
                                
                                                                                 
                      
                                                                                            
                     
                     
                                                          
                                                                                                  
                                                      
                                 
                      
          
                                                 

                                                                                     
                                                                                   
                                         
                                                         
                                   

                                 
                                        
                                                                                   
                                                                 
                                                                                              
            
      

                                                                      
                                                                                                    
                  
                
                
                              
             
                                              
                                                                                       
                                                
                                                          
                                                          
               
            

                                                  
                                                                             
           
                            
                                              
                          
                       
               
                                                 
                                      
                                                                                              
                   
              
                                   
                                                           
         
                                                                                       
                                            
                                                                                
                              
                                                       
                            
                                                     
                
                             

                                                                                                 
                                                          
                                                                                         
                                             

                                   
                                   
               
                                                 
                                                      
                                  
                                 
                                         
                                                                          
          

                                   
                                   
                                                                                          
                               
                                        
                                                               
                                                                                   
                              
            
                                                                            
                                                                           
                                                                              
                                                       
                           

                                                            

end LeanLab.VanDerCorput1939
