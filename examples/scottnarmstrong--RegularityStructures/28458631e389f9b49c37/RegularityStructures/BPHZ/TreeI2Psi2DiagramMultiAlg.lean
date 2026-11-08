/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.TreeI2Psi2DiagramAlg

/-!
# Elementary inequalities between powers of three scales, general exponents

Let `0 < r, r' ≤ 1` (the scales `s(y - x)`, `s(y' - x)`), `d > 0` with `d ≤ 8 (r + r')` (the scale
`s(y - y')`).  The inequalities of `TreeI2Psi2DiagramAlg` are generalised to a free
homogeneity loss `ℓ ∈ [0, 1/2]` and a free top power `p`:

* `alg_max_key`: `(max r r')^α d^(-β) ≤ d^(-p) (r^(p-ℓ) + r'^(p-ℓ)) + 4 d^(-ℓ)` for
  `0 ≤ β ≤ p`, `β - ℓ ≤ α`;
* `alg_pair_key`: the same for `r^g r'^g d^(-β)` with `β - ℓ ≤ 2 g`;
* `alg_pat`: the product of two single integrals, one with a loss `σ`, bounded by `136` times
  `d^(-2) (r^(2-ℓ) + r'^(2-ℓ)) + d^(-ℓ) + r^(-ℓ)`.
-/

public section

namespace RegularityStructures

                                                                              
                                           
                                                  
                                         
            
                                                                                           
              

                                                                
                                                                          
                                                                                 
                      
                                                                  
                                                                              
                                                     
                                                                  
                                                 
                                             
                                                                                       
                              
                                                 
                                                              
                
                    
                                         
                                                                     
                                                    
                                     
                                                           
                                                                                  
                                                  
                                                                
                                                  
                                             
                                                                     
                                                                                   
                                                  
                                              
                          
                                                           
                                                                                  
                                           
                                                                                  
                                                       
                                                                                        
                            
                
                                      
                                                 
                                                                  
                               
                                             
                                                          
                          

                                                                       
                                                                                  
                                                                                        
                                                  
                               
                                                                  
                                                 
                                            
                                    
                            
                             
            
                                                    
                                                
                                                    
                                         
          

                                                                                     
                                                                                   
                                                                                    
                                                                       
                                                                                            
                                                                  
                                   
               
                                                    
                                                 
                                                          

                                     
theorem rpow_mul_rpow_le_add_two {r r' g : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    r ^ g * r' ^ g ≤ r ^ (2 * g) + r' ^ (2 * g) := by
  have h1 : (r ^ g) ^ 2 = r ^ (2 * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have h2 : (r' ^ g) ^ 2 = r' ^ (2 * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr'.le]; congr 1; push_cast; ring
  nlinarith [sq_nonneg (r ^ g - r' ^ g), Real.rpow_nonneg hr.le g, Real.rpow_nonneg hr'.le g]

                                                                   
                                                                                   
                                                         
                                                                                    
                                     
                                                  
                                          
        
                                                   
           

                                                                    
                                                                      
                                                                                          
                                                                                 
                                                      
                                                               
                                                                                       
                                    
                                                                         
                                                                     
                                                                     
                                                        
                                          
                                                                      
                                                                                        
                                                                      
                                                                       
                                                                                      
                               
        
             
                                                                                     
                        
                                                                                        
                                                                
                                                                                          
                                                            
                                                    
              
                                                                           
                                          
                                                   
              
                                     
                             
                              
              
                                                                              
                                                                    
                                      
                                         
                                                                        
                                  
                                                                    
                                              
                                                                                               
                                        
                                                                      
                                                                                 
                                                                                          
                                                                                         
                                     
                                                                                     
                                                                                        
                                                                
                                                                                
                                  
                                                    
                                                    
          

end RegularityStructures

end
