module

public import Mathlib
public import LeanLab.VanDerCorput1939.Statements

/-!
P0067 van der Corput 1939: the constant K of (2) converges, and the global form of the
singular series, K P(N) = ∏_{p ∣ N} (1 − 1/(p−1)²) ∏_{p ∤ N} (1 + 1/(p−1)³) for every N ≥ 1.
For odd N every factor is positive, so K P(N) > 0; for even N the factor at p = 2 is 0, which is
why (1) is stated for odd N only.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.VanDerCorput1939

open Real Finset

attribute [local instance] Classical.propDecidable

                                                                                       
                               
                                                                                                
                               
                    

                                               
                        
                                                                             
                                       
                                                              

                                                                                               
                                              
                                                   
                                                                       
                                     
                                     
                     
                         
                       
                                  
                                                     

                                
                                       
                                                                        

                                                                                  
                                      
                                                               
                                                                      
                                            
                                                                
                                                                                
                                   
              
                                                                   
                                                
                              
                                                                
                                  
                          
            
                                                                                             
                                                                                 
                                                                                 
                                     
                      
                          
                
                                                         
                                                                         
           
                                  
                    
                                  
          
          
                                            
                       

                                                   
                                                                        
                              
                                                             
                     
                  
                                
                                                                                        
                                     
                                                                    
                                              
                                                                  
            
                                          
                                                              
            

                                                                                       
                                    
                                                                            
                                 
                                                                         
                                                        
                     

end LeanLab.VanDerCorput1939
