/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.Statement
public import Mathlib

/-!
# Dyadic cubes in the plane

Adapted from `FalconerPacking.Dyadic` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Dyadic.lean
This is the geometric cube hierarchy used in the finite gauge Frostman construction.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge.GaugeFrostman

/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}

                                                           
                                                                                               

                                                                                   
                                                
             
           
            
                                               
             
                                                       
             
                                                  

                                                                                                             
                          

                                                          
                                                                     
                                                     
                                                
                                                          

                                                        
                                                               
                                                           
          
                                                                        
             
        
                                                     
          

                                            
                                                                       
                                                                                 
            
                                                                                 
                                
                                                  

                                                            
                                                                                          
                                                         
                                              
                                              
                                                        
           
                   
                   
                                                   
                 
                                                        
                                       
                                   
            
                             
                                                                         
                                                                                
             
                       
                                                           
                                                                           
                                             
                                         
                                 
                                            
                                                                       
                                       
                                                                                   

                                                          
                                        
                            
                                                                                                             
         
                                  
           
                                        
                                                                                             
                               

section Counting

                                                              
                                                                                                         
                             
                                                                
                                                            
                                                   
                                                  
                                             
                     
                                                                
                                     
                                                                      

                                                                                               
                                                                                              
             
                                                                                               
                                            
                               
                                                   
                                                             
                                              
                                            
                                                                        
                                                                                               
                                         
                
                              
                                                           
                                                                                         
                   
                                                                        
              
                                    
                                                   
                                                          
                             
                                                      
                                                            
                                                      
                                                      
                                                              
                                                                                              
                     
                          
                                                                                              
                                                                              
                                                                                  
                                                            
                      
                                                                       
                              
               
                    
         
                                                          
           
                                             
                       
                           

                                                        
                                                                                         
                                            
                                                
                                                          
                                                                            

end Counting

section Ancestors

                                                               
                                                                       

                                                                      
          
                 

                                               
                                                           
          
                      
                                                                              

                                                                                   
                                                          
                                                               
            
                                                               
                                
                              

                                                                           
                                                              
                                                            
                                 
                
                
                
                                                   
                                                        
                                                          
                                        
                                   

                         
                                                     
                                                        
          
                      
                                                                       

end Ancestors

end FalconerThetaGauge.GaugeFrostman
