/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer geometry for the lacunary middle range

This module formalizes the combinatorial core of the lacunary positive-endpoint
argument in arXiv:2609.04101v1. We write the paper's fixed support constant as
`C₀ = 2^c`, where `c : ℕ`, and take the cutoff/block length `B` to be a natural
number. After taking base-two logarithms, the paper's ranges become

* `L B c m = {j : m + 2j ≤ -c - 2B}`;
* `S B c m = {j : -c - 2B < m + 2j ≤ c + 2B}`;
* `Q B τ = [τB, (τ+1)B) ∩ ℤ`;
* `R B c τ = ⋃ m ∈ Q B τ, S B c m`.

All bounds below are explicit. In particular, `S` has between `2B + c` and
`2B + c + 1` elements, `Q` has exactly `B` elements, and `R` has at most
`5B` elements as soon as `2c ≤ 5B`. The paper's sparsification modulo
`10^10` gives pairwise disjoint frozen ranges.
-/

namespace QuadraticCarleson.LacunaryMiddleRange

set_option autoImplicit false

/-- The paper's very-small atom scales `L_{k,m}`, in additive dyadic coordinates. -/
def L (B c : ℕ) (m : ℤ) : Set ℤ :=
  {j | m + 2 * j ≤ -(c : ℤ) - 2 * (B : ℤ)}

/-- The paper's middle atom scales `S_{k,m}`. The displayed endpoints are the
integer solution set of `-c - 2B < m + 2j ≤ c + 2B`. -/
noncomputable def S (B c : ℕ) (m : ℤ) : Finset ℤ :=
  Finset.Icc ((-(c : ℤ) - 2 * (B : ℤ) - m) / 2 + 1)
    (((c : ℤ) + 2 * (B : ℤ) - m) / 2)

                                                               
                                                 
                                              

                                                                            
                                               
                                                   
                         

                                           
                                                       
         

                                   
                 
                                          
                                               
                               
       

                                 
               
                                                       
                                                 

                                                                             
                                                       
                                                             
                 
                                                           
                   
       

                                                                  
                                                
                 
                                                          
                                                         
             
            
                                           
                                
                     
                     
         
           
                            
                                                     
                         
                                               
                  
                 
             
                  
                         
                 
             
                                                 
                  
                           
             
                  
                   
             

                                                         
                           
            
                                          

                                                                        
                                                                 
                                  
                                                         
                                                                     

                                                                     
                                                          
                             
                                               
                              
                                
              
               
                                           
                                                 
              
                    
                     
                    
                                                     
                                                   
                                                    
               
                    
                                                     
                                                    
               

                                                       
                      
                                                       
           
      

                                                                    
                                     
                                        
                      
       

                                                                          
                          
                                     
                                    
                      
       

                                                 
                        
                                                        
                                                       
       
               
                            
       

                                                                                 
                                                        
                                                  
                                      
       

                                                                                  
                                                         
                          
                                
                                      
       

                                                                             
                                                        
                                  
                                  

                                                            
                        
                                                               
                     
                     
             
                       

                                            
                           
                                                      
            
                                                                
                       
        
                            
          
                                 

                                                               
                                 
                       

                                                                                 
                                                       
                           
                                                    
                                         
              
                                                                    
                    
                            
                    
                                
                     
          

                                                           
                                                             
                                       
                           
                
                                      
                                       
                                            
             
                                    
                                                            
                                                             
                                                 
       

                                                            
                                    

                                                          
                                          
                                  
                                
                          
                        
               
           
              
         
                            
                           
         
                                                      
                            
                          
       

                                                               
                                                         
                                                    
                                    
                                             
                                 
       

                                                                            
                                                                         
                 
                                                           
                                                    
                                          
                                       
                                            
                                             
                                 
       

end QuadraticCarleson.LacunaryMiddleRange
