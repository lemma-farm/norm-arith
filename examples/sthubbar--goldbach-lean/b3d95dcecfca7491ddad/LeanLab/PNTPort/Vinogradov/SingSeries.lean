module

public import LeanLab.PNTPort.Vinogradov.TernaryAssembly

/-!
# The truncated ternary singular series in Ramanujan sum form

Lab proof, unit U-5257. AI wrote this file. Known mathematics, no cited input.

* `ramanujan_sum`: `∑_{r < q, (r, q) = 1} e(nr/q) = c_q(n) = ∑_{d ∣ (n, q)} d μ(q/d)`, the lab's
  `HeathBrown1985.ramanujan`.
* `singP_eq`: `𝔖_P(n) = ∑_{q ≤ P} μ(q)³ c_q(n) / φ(q)³`, real.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve

                                             
                                                    
                                                                      
                                              
                 
                                                                              
                                                                   
             
                                        
                           
                      
                          
                                                                                      
                                                                                                     
                                                                                          
                
                                                    
                                                    
                                                                            
                                                 
             
                                                                       
                  
                                        
                      
                                                  
                  
                            
                                  
                                      
                                                 
                                             
                  
                             
                                      
                                                      
                  
                             
                               
                                                                                        
               
                 
                  
                            
                                                       
                                   
                           
                                                                                  
                                                                                          
                                                                                     
                                                                                   
                                                                     
                
                                             
                           
                                                                                   
                                                       
                
                                 
                                                    
                                                    
                                                              
                                       
                                                     
                                                              
                
                                             
                                              
                
                                 
                                                                  
                
                                             
                                                          
          
             
                                                                               
                          
               
                                                               
                                                               

                                      
                            
                                                                               
                                         
                     
                              
           
                                     
                    
                                                             
                                                                   
                                                             
                                                                
             
                                     
                                               
                                       
                                                                                           
                                                       
                                                         
                            
                                   
                                            
      

end LeanLab.PNTPort.Vinogradov

