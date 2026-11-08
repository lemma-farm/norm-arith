import MoltResearch.Discrepancy.SingularSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Discrepancy: L-function bounds for the character sums

Nucleus module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`, issue
#2871, PR E1): the `L`-function inputs of the non-principal character-sum estimate.

- `zetaWeightedSum_char_eq_LFunction`: the zeta-weighted sum of a Dirichlet character *is*
  the analytically-continued `L`-value at `σ > 1` (junk conventions align: both kill `n = 0`).
- `exists_norm_LFunction_le`: for non-principal `χ`, `‖L(χ, σ)‖` is uniformly bounded on
  `σ ∈ [1, 2]` — Mathlib's analytic continuation (`differentiable_LFunction`) plus
  compactness. This replaces the paper's "`L(s,χ₁)` is analytic near `s = 1`" remark.
- `exists_re_tsum_primes_char_le`: consequently the character prime sums
  `Re ∑'_p χ(p)/p^{1+1/log X}` are bounded uniformly in `X ≥ 3` — through the
  log-linearization of `SingularSeries.lean`, modulus-only (no branch-of-log issues).

The finitely-many-characters pattern (`NonPretentiousUniform.eventually_nonPretentiousAt`
style) lets §4 take a single constant over all `χ₁ mod r`, `r ∣ q^k`, since `q, k` are
fixed before `X`.
-/

namespace MoltResearch

open Finset

variable {N : ℕ} [NeZero N]

                                                                      
                                                               
                                                                            
                                                      

                                                                                  
                                                                                     
                                                                                             
                                                   
                                                    
                                                                                              
                               
                                   
                                                                
                                                                                      
               
                                   

                                                                                          
                                                                               
                                                                            
                                             
                                                        
                                                                                 
                            
                                                                     
                                             
                                                        

                                                                                    
                                                                         
                                                                  

                                                                                        
                                                                                         
                                                                                 
                             
                         
                                    
                                                                          
                                               
                                     
            
                                                
                                                
                                     
                                 
            
                                                  
                                                       
                                                
                 
               
              
                              
                           
               
              
                              
                                                       
                                               
                                             
                                                              
                                           
                                                     
                                                     
                                 
                                                                                       
                                 
                                                                    
                                                                              
                                  
                          
                                                                         
                                                        
                                                                       
                                             
                                                       
                                                                 
                                                                   
                                     
                                                               
                                             
                                                    
                               
                                                     
                          
                                  
                                                              
                   
                                      
                                             

end MoltResearch
