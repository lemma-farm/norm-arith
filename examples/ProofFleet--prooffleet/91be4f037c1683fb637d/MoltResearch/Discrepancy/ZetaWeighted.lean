import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Discrepancy: zeta-weighted sums and the Euler product bridge

Language-layer module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`,
issue #2871): the zeta-type weighted sums `∑_n g(n)/n^σ` (the paper works at
`σ = 1 + 1/log X`, whose mass `∑ n^{-σ} ≍ log X` acts as a smooth truncation at `X`), and
their Euler products for completely multiplicative 1-bounded `g`.

§4 uses these for the singular series `𝔖 = ∑_n h(n)/n^{1+1/log X}` of the pretentious part
`h` and its character-twisted variants (residue-class equidistribution mod `q^k`).

Encoding notes:
- Junk values: the `n = 0` term is `g 0 / 0^σ = 0` by ℂ-division junk once `σ ≠ 0`
  (`Complex.zero_cpow`), so tsums over all of `ℕ` are safe.
- The bridge to Mathlib's Euler-product machinery is
  `CompletelyMultiplicativeC.zetaWeightHom`: for guarded-CM `g` with `g 1 = 1` the weight
  `n ↦ g n / n^σ` is a genuine `ℕ →*₀ ℂ` — the `0`-guards (issue #2879) cost nothing here
  because the weight vanishes at `0` on its own.
-/

namespace MoltResearch

                                                                                           
                                                                                       
                                                            
                                   

namespace CompletelyMultiplicativeC

variable {g : ℕ → ℂ}

                                                                                      
                                                                                        
                                                                                          
                                                                                  
                                        
                                    
                 
                                                                                   
                           
                    
                                     
                       
                                                              
                                     
                       
                                                              
                                                    
                     
             
                                                           

                                                                                      
                                  
                                                          
     

end CompletelyMultiplicativeC

                                                                                   
                                                                       
                                                                                           
                                                     
                                   
                                                                                       
                                                                
                                                                     
                                                                                  
                                                                 
                                                                           

                                                                                        
                                                                                         
                                                         
                                                          
                                                               
                                             

                                                                                        
                                                                                      
        

                                        

                                                                                             
                                                                                           
                                                                
                                                                               
                                                           
                                                                              

end MoltResearch