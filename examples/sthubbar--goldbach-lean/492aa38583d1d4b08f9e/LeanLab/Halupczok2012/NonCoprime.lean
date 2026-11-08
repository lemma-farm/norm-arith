module

public import LeanLab.Halupczok2012.Statements

/-!
# Halupczok 2012, Theorem 1.2: the all `q` form with a vanishing main term

AI wrote the Lean code, Claude, Anthropic. Binary Goldbach is open; ternary Goldbach is a
theorem, Helfgott 2013.

The defect. As printed, Theorem 1.2 of the paper, JTNB p. 333, sums over all `q ≤ Q` with no
condition `(a, q) = 1`, its right side is `≪ Y₁ Y₂ L^{-A}` with no factor `Q`, and the printed
`T(n, q, a)` does not vanish when `(a, q) > 1`; for example `T(n, 3, 3) ≈ 0.767`. For such `q`
the prime sum is empty once `q ≤ X₁`, so the single term `q = 3` at `a = 3` is about
`0.767 Y₁ Y₂`, larger than the claimed bound. The proof says it assumes `(q, a) = 1` without
loss of generality.

The repair. Take the main term to vanish when `(a, q) > 1`, as the binary singular series
`S(r, q, a)` of the paper's display 1 does. `T0` is that convention. Then each non-coprime
prime sum is exactly zero once `q ≤ X₁`, since the only candidate `p₁` is a prime factor of `q`,
below `X₁`.

* `ternSum_noncoprime`: for `1 ≤ q ≤ X₁` and `(a, q) ≠ 1` the prime sum of Theorem 1.2 is `0`.
* `theorem2Zeroed_of_theorem2`: the coprime `Theorem2` implies `Theorem2Zeroed`, the sum over
  ALL `q ≤ Q` with `T0`, under the extra hypothesis `Q ≤ X₁`, which the paper's
  `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives for large `X₁`. Adding `(a, q) = 1` to the printed statement is
  the same theorem restricted to coprime `q`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

                                                                                  
                                                                                    

                                             
                                                                           
                                                                                     
                
                          
            
         
                              
                                                  
                                                    
                                                                                                  
                                                     
                                                                                          
                                                     
                                                   
                                                          
          

                                                                         
                            
                                                                     
                                                                           
                                                                                          
                                                                                               
            
                                                                      
                                        

                                                                    
                                                                        
                               
                                                    
                                         
                                            
                                                                
                                                  
                                                                                               
                                                                                
                                                                
                            
              
                                                
                                 
                                                                   
                                                  
                 
                      
                                                                               
                                                        
                                                                     
                                                           
                              
              
                                
                   
             
           

end LeanLab.Halupczok2012
