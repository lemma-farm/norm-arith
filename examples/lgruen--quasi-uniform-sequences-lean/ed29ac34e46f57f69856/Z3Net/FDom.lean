module
public import Z3Net.FBasic
public import Z3Net.SUSep
public import Mathlib
@[expose] public section

/-!
# Entry F, part 12: `prop:D` (diagonal dominance) for an arbitrary design

Every `b_i` of `lem:Ss` is `max(0, |e_i q + t| - jit_i)` for a representative `t ≡ σ_i (mod q)`,
`|t| < q` (`bval_spec`); with dominance every moving coordinate is backward with `|σ_i| ≤ 2a`,
and the own-axis step has `|σ_i| = α_i ≤ a`; then entry U's abstract `key_sym` applies.
-/

namespace Z3NetF.Proofs

open Finset

noncomputable section

                                                                                                
                                 
                                                            
                                                                                                             
                                                
                                 
                                                                
                                                            
                                                        
                                                           
                    
              
                               
                                                             
                           
                              
                  
                                                                                                                    
                                                                           
            
                                                                             
                                                                      
                             

                                                                                     
                                                                   
                    
              
                                                                                                

section dom

variable {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (α : Fin s → ℕ) (a : ℕ)

                                                                                                 
                                                    
                    
                                                                                                       

                                              
                                                    
                                                                        
                                                                                
                                                                                       
                                                 
                   
                              
                                                                                                        
                                         
                        
           
                                        
              
                                                        
                                                     
                                                                                 
                          
                                                                             
                                                            
                                                                                                       
                                                    
                                      

                                                                                        
                                                 
                                                 
                                                                           
                     
                                                                            

                                                
                                                                         
                                                    
                                                                        
                                                        
                                     
                                                                                               
                                                        
                                         
                                           
                             
                              
                                                               
                                                                                                     
                                                                      
                                         
              
                                    
                                                   
                                                      
                                                                            
                     
                                                                                                   
              
                                           
              
                                           
                   
                                                                       
                                                                                     
                                                      
                                                                                                       
           
              
                     
                                                  
                            

end dom

end

end Z3NetF.Proofs
