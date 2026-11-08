/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Value

-- Used only inside proofs.
import Mathlib
import Mathlib.Tactic.LinearCombination

/-!
# The estimates (3.1)–(3.4) of Bugeaud 2013

Fix `w ≥ 1`, a period `r ≥ 1` and a length `u ≤ r` such that `a_m = a_{m+r}` for
`w < m ≤ w + u`. The paper's `P_n` is the polynomial `A X² - (B₂ + B₃) X + C` with

```text
A  = q_{w-1} q_{w+r} - q_w q_{w+r-1},   B₂ = q_{w-1} p_{w+r} - q_w p_{w+r-1},
B₃ = p_{w-1} q_{w+r} - p_w q_{w+r-1},   C  = p_{w-1} p_{w+r} - p_w p_{w+r-1},
```

the integer point `v_n = (A, B₂, B₃, C)`; everything is stated at `w = j + 1`. This file proves
the bounds on the linear forms of §3 at `v_n`:

* `|α A - B₂| ≤ 2 q_w / q_{w+r}` and `|α A - B₃| ≤ 2 q_{w+r} / q_w` ((3.2), (3.3));
* `|A|, |B₂|, |B₃|, |C| ≤ q_w q_{w+r}`;
* **(3.4)** `|P_n(α)| ≤ 12 (q_{w+r} / q_w) q_N⁻²`, `N = w + r + u`, from (3.1) and the root
  `α_n` of `P_n` (the continued fraction completed by periodicity);
* the products of the forms of the two Subspace applications are at most
  `48 q_{w+r}² / q_N² ≤ 96 · 2^{-u}`.

## Main definitions

* `Nat.spadeVec a j r`: the point `v_n = (A, B₂, B₃, C)` for `w = j + 1`.
* `Nat.spadeExt a j r`: the continued fraction completed by periodicity (the paper's `b^{(n)}`).

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, §3.
-/

@[expose] public section

namespace Nat

                                                                                            
                                  
                                                 
                                                                                
                                                                                
                                                                                
                                                                                

                                                                                          
                                                  
                                                 
                                                          

variable {a : ℕ → ℕ}

                                                                
                                                                                      

                                                               
                                                                                      

                                                               
                                                                                      

                                                                 
                                                                                      

                                                                     
                                                   
                                                                                            
                                                                         

                                                                    
                                             
                                                                     
                                                           
                 
                  
       
                                                                     
                                                                               
                                                
                                              
                                                                                   
                                                             
                                                        

                                                                 
                                                                                       
                                                              
                                 
                                                                    
                                
                        

                                                                  
                                                                                               
                                                                          
                                
                                               
                                                                                                 

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `|q_ℓ α - p_ℓ| ≤ 1 / q_{ℓ+1}`, the non-strict form of (2.2). -/
theorem abs_contDen_mul_contFrac_sub_le (n : ℕ) :
    |(contDen a n : ℝ) * contFrac a - contNum a n| ≤ 1 / contDen a (n + 1) := by
  rw [one_div]; exact (abs_contDen_mul_contFrac_sub_lt ha n).le

theorem contDen_mono_real {m n : ℕ} (h : m ≤ n) : (contDen a m : ℝ) ≤ contDen a n := by
  have : Monotone (contDen a) := monotone_nat_of_le_succ (contDen_le_contDen_succ ha)
  exact_mod_cast this h

                                                                               
                                        

                                                
                                  
                                                                                               
                   
                                                                                              
                                                           
                                                           
                                                       
                                               
                                            
                         
                                                                                   
                 
                                                                                               
                                                                                  
                                                                                      
                   
          
                               
                                   
                                                                                                   
                                                                       
                                                                                                  
                                                            
                                                                      
                    

                                                
                                  
                                                                                               
                   
                                                                                              
                                                           
                                                 
                                                       
                                        
                         
                                                                                   
                 
                                                                                               
                                                                        
                                                                                      
                   
          
                               
                                   
                                                                                            
             
                                                                                                
                                                                          
                                                            
                                                                      
                    

                                                                            
                                               
                                                                              
                                                 
                                                                   
                                         
                                               
                                               
                                                   
                                                             
                                                             
             
                                             
                                 
                                                                        
                                             
                                
                                                                               
                                             
                                
                                                                               
                                             
                                  
                                                                                      

                               
                                        
                                                                                  
                                   

                                                        
                                                                                  
                                        
                                            
              
                            

                                                                                                   
                                                                                             
                                                             
                                                               
                                              
                                                                                    
                                                                                                    
                     
                         
                                            
                                      
                
                                                
                                                                                                  
                                                                          
                           
                        
                                                             
                                                                                                 
                                                          
                                                           
                                             
                                                                       
                                                                          
                                                                                    
                                                                  
                     
          
                                                                                             
                                   
                                   
                                     
                                     
                                      
                                      
                                     
                                                                                             
                      
                                                                                               
                      
                                                                                               
                      
                                                                                             
                      
                         
                         
                                                       
                                                                         
                                                                 
                                            
                                                                 
                             
                   
          
                                        
                                            
                                  
                                                                                               
                                                                                         
                                                        
                                          
                                        
                       
                                                                                       
                                                            
                                                                          
                              
                                        
                                                       
                                        
                              
                                                                                              
                                                               
                                                                                                 
                                                             
                                                                      
                            
                              
                                                                    
                                                                               
                                                            
                                                
                                                             
                                                 

                                                                 
                                                        
                                                                         
                                                       
                                            
                                                 
                                                                                   
                    
                                              
                                                                                              
                 
                

                                                     
                                                      
                                                                 
                                                               
                                              
                                                                                      
                                                                
                                                                                         
                        
                                          
                                  
                                  
                                     
                                                 
                                        
                                            
                                                
                                       
                                           
                                               
                                                                                      
              
                  
                  
                                                     
                                     
                             

                                                                                          
                                                       
                                                                  
                                                               
                                              
                                                                                      
                                                                                         
                        
                                          
                                  
                                     
                                                 
                                        
                                            
                                                
                                                                                               
                                       
                                           
                                               
                                                                      
              
                
                                                      
                                          
              
                                                                                             
                                                   
                                                            
                                                  
                                           
                             

end Positive

end Nat
