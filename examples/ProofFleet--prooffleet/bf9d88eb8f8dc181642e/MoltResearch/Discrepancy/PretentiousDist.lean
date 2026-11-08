import MoltResearch.Discrepancy.LogAvgCorr

/-!
# Discrepancy: pretentious (Granville–Soundararajan) distance, finite-`N` form

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the finite-truncation pretentious distance used to state the non-pretentiousness hypothesis of
the logarithmically averaged Elliott theorem (arXiv:1509.05422):

`𝔻(g, h; N)² = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

Conventions:
- The prime range is `Nat.primesBelow N` (primes strictly below `N`) — the Mathlib-idiomatic
  finite prime truncation; interfaces quantifying over all `N` are insensitive to `< N` vs `≤ N`.
- The **squared** distance `pretentiousDistSq` is the primary definition (the literature works
  with `𝔻²` throughout); `pretentiousDist` is its square root.
- Junk values are embraced: without unimodularity hypotheses the summands can be negative, so
  the order lemmas below carry `Unimodular` hypotheses rather than baking them into the
  definition.

Monotonicity basics (this module deliberately stops here):
- `pretentiousDistSq_summand_nonneg`, `pretentiousDistSq_nonneg` — nonnegativity for unimodular
  arguments.
- `pretentiousDistSq_mono` / `pretentiousDist_mono` — monotone in the truncation `N`.
- `Unimodular.pretentiousDistSq_self` — the diagonal vanishes (each summand is `0`).
-/

namespace MoltResearch

/-- Squared finite-`N` pretentious distance (Granville–Soundararajan):

`pretentiousDistSq g h N = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

The non-pretentiousness hypothesis of the log-Elliott interface says this tends to `∞` with `N`
for every character-modulated comparison `h`.
-/
noncomputable def pretentiousDistSq (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, (1 - (g p * (starRingEnd ℂ) (h p)).re) / p

                                                                               
                                                              
                                     

                                                  
                                                                                          
                          

variable {g h : ℕ → ℂ}

                                                                                     
                                                                                            
              

                                                                                          
                                                                                              
                                            
                                                                           
                                       
                                                        
                  
                                                         
                                           
                                                                 
                                                                      
                     
            
                           

                                                                                   
                                                                                          
                                                     
                                                                           

                                                                                    
                                                                   
                                       
                                  
                                                                                      

                                                                                  
                                                                                  
                                  
                                                                   

                                                                                      
                                                           
                                                                 
                                                       
                                                           
                                             
              
                                    
                                         
               
                                                                 

                                                                      
                                                                          
                                                                                
                   
                                                        
                                                                   

                                                                                      
                                                                                   
                    

                                                                                         
                                                                              
                   
                                                    
                                                      

namespace Unimodular

                                                                                     
                                                 
                                                            
                                     
                          
                                         
                         
      

                                                        
                                                          
                                   
                                                                   

end Unimodular

/-! ### Quasi-triangle inequality

The sharp Granville–Soundararajan triangle inequality for `pretentiousDist` is not needed by
the derivation-(C) bookkeeping (all its pretense bounds are `O(1)`), so we state only the
elementary squared-distance version with constant `3`, which has a pointwise proof on the
closed unit disc. -/

                                                           
                                                                  

                                                                                         
                                                           
                                                                                       
                                                                          
                                          
                                         
                                                        
                                  
             
                                          
                                         
                                                        
                                  
             
                                                           
                                                           
                                                                          
                         
           
                                                                                 
                                                         

                                                                  
                                                                                    

                                                                                  
                                                                                            
                                                                              
                    
                                  
                                                                                         
                                            
                                                        
            
                                                                               
                                   
                                   
                                                        
                                                                      
                                                       
                                                                          
                                                     
                                        
                
                                              
                                                
            
                                              
                                                
            
                                                         
                     
         

                                                                                     
                                                                                        

                                                  

                                                                                           
                                                                                         
                                                                               
                                                                            
                                                                     
                             
                                                                         
                          
                                                               
                                         
                                
                                                    
                                                                 
                                                   
                                                    
                                                                  
                                                     
                                                         
                                                                      

                                                                                       

                                                                                           
                                                                                          
                                                                                      
                                                                                   
                                                           

                                                                                       
                                                                                    
                                 
                  
               
                                                                      
                                                         
                                            
              
                                                          
                 
                                   
                                                          
                                                                           
                                                         
                           
                                                           
                                                               
                      

                                                                                               
                                                                                               
                                                                                                
                                       

                                                                                                
                                                                                            
                                                          
                                                 
                                                                           

                                                                     
                                                                     
                                                           
                                                               
                                               
                                                         
                               
                                   
                                                        
                                                           
                                         
                                                      
                            
                                
                       
                                                       
                            
               
                                                 
                                                  
              
                            
                                   
                                  
                     
                            
                            
                   
                                                                 
                   
                                                            
                                                       
                
                
          
                                          
           
                                             
                                                              
                                              
                                                                                  
                                                       
                        
                                              

                                                                    
                                                                      
                                                                      
                                                                     
                                         
                                                   
                                                                         
                           
                               
                                           
                                                     
           
                                                 
              
                                    
                          
                          
                              
                                                               
                                      
                                           
                                
                                                    
                                                
                                                                
                                           
                         
                                                             
                                                     
                                                           
                                             
                                                                     
                                                                        
                                                                         
                          
                                                            
                           
                       
                                                                            
              
            
                              
                   


end MoltResearch
