import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Discrepancy: completely multiplicative functions from prime data

Language-layer constructor for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`,
issue #2871): the unique completely multiplicative extension `n ↦ ∏_{p^k ∥ n} F(p)^k` of a
prescribed function on the primes.

§4 uses it twice, to split a pretentious sample `g = χ̃ · n^{i𝐭} · h`:
- `χ̃`, the *character-like* completion of a Dirichlet character `χ` mod `q`: `χ(p)` at
  `p ∤ q`, but the (unimodular) `g(p)·p^{−i𝐭}` at `p | q` — the generalized
  Borwein–Choi–Coons object whose medium-length sums §4 bounds below;
- `h`, the *pretentious-to-1* part: `g(p)·conj(χ(p))·p^{−i𝐭}` at `p ∤ q`, `1` at `p | q`.

Conventions:
- Junk values: `cmOfPrimes F 0 = 1` (empty factorization), consistent with the guarded
  `CompletelyMultiplicativeC` (issue #2879), which never constrains the value at `0`.
- Only the values of `F` **at primes** matter (`cmOfPrimes_apply_prime`); unimodularity of
  the extension needs `‖F p‖ = 1` at primes only (`cmOfPrimes_unimodular`).
-/

namespace MoltResearch

                                                                                    

                                                                                        
                                                   
                                                  

                                                                                 
                                                                      
                   

                                                
                                                                     
                   

                                                                                     
                                                          
                                                  
                 
                   
                                  
                                                                                        

                                                    
                                                                   
                              
                   
                                                                      
                                              
                                             

                                                             
                                                                               
                                        
                   
                                     
                                                  

                                                                                        
                                      
                                                                               
                                   
         
                   
                              
                                          
                                                         
                                      
                                  

end MoltResearch
