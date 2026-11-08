module

public import LeanLab.PNTPort.Vinogradov.MinorArcs

/-!
# The ternary circle method on `ZMod M`, and the minor arc contribution

Lab proof, unit U-5253. AI wrote this file. Known mathematics, no cited input.

* `circle_identity`: for any `Φ : ZMod M → ℂ`,
  `∑_k (𝓕Φ(k))³ e(nk/M) = M ∑_{a + b + c = n} Φ(a)Φ(b)Φ(c)`.
* `ternary_minor`: with `Φ = Λ 1_{[1, N]}`, `N < M`, the minor frequencies contribute at most
  `M B ∑_{n ≤ N} Λ(n)²`, `B = 300 (N/√P + N^{4/5} + √(NQ)) (1 + log N)⁴`; so
  `‖M r₃(n) - ∑_{k major} (𝓕Φ(k))³ e(nk/M)‖ ≤ M B ∑ Λ²`, unconditionally.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open scoped ArithmeticFunction.vonMangoldt

                                     
                                                                             
                                                             

                                                                          
                                                                         
                                                                   
                                                                                   
           
                             
                                             
                                                                                        
                                                                                          
                                                                   
                                                                                       
                   
                  
                                     
               
            
              
                                    
                        
                                    
                        
                                    
                                                         
                            
                                                   
                                                                                          
                     

                                  
                                                                                      
                                
                                 
                                                        
                                                          
                                                                                      
                                            
                                                                    
                                                                                        
                                      
                                                                                            
                         
                                                                              
               
           
                                   
                                                                                     
                                    
              
                                                 
                                                               
                                        
                                                          
                                                                       
                                                                                    
             
                                                     
                        
                                     
                                                     
              
                                                                
                              
                                                                              
                                                                       
                                        
                                                                                 
                                                                                 
                            

                                                                                        
                                     
                                              
                                                

                                                                
                                                                           
                                                    
                                                                            
                                                                                               
                                                                                          
                                                    
               
                                                                
                                                                
                                                                
                          
             
                                       
                                         
                                           
                                                                              
                                                        
                                                                                
                                                                                
                                  
                                                
                                            
                                                           
                        
                      
                    
            
               
                                                                               
                                    
                                                         
                                                                                   
                       
                 
                       
                                        
                                        
                                                            
                                                                  
           
           
                                     
                                                             
                                        
                               
                                                                           
                                     
                                           
                                                                 
                                         
                                     
                          
                                                      
                                 

                                                                                            
                                                                                    
                                        
                             
                                                        
                                                                     
                                                                                      
                                            
                                                                    
                     
                                                       

end LeanLab.PNTPort.Vinogradov

