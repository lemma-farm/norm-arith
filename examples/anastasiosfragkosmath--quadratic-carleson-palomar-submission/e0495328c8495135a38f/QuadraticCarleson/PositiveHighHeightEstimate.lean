/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.QuadraticFixedHeightAveragingNorm
import QuadraticCarleson.CalderonZygmundLevelAtoms
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Genuine high-height estimate: disjoint level-atom inputs

The paper's high part uses the strict height range `r > B_k` and the input
`b_k = ∑ I, b_{I,k}`. This file constructs that countable disjoint atom sum,
proves its L² input bound from the actual atom estimates, and invokes the
proved real-parameter fixed-height quadratic maximal theorem.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration

noncomputable def disjointLevelAtomSum {ι : Type*}
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ι → ℝ) (x : ℝ) : ℂ :=
  ∑' i, levelAtom A f k (z i) (R i) x

theorem levelAtom_eq_zero_of_other_mem {ι : Type*}
    {A : ℕ → ℝ} {f : ℝ → ℂ} {k : ℕ} {z R : ι → ℝ}
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i)))
    {i j : ι} (hji : j ≠ i) {x : ℝ} (hx : x ∈ centeredInterval (z i) (R i)) :
    levelAtom A f k (z j) (R j) x = 0 := by
  apply levelAtom_eq_zero_of_not_mem
  intro hxj
  exact Set.disjoint_left.mp (hdisj hji) hxj hx

                                                                       
                                            
                                                 
                                                                         
                                           
                                          
                                                   
           
                                                     
                        
                                                               
                                                             
                                                  
                                                          
                                                          
             
                                                              
                                       

                                                                 
                                               
                                                                             
                                                                       

                                       
                                               
                                                    
                                          
                                                                                    
                                                                                 
                                                           
                                          
      
                                                                       
                          
             
                
                  
                                         
               
                                                   
             
          
                                                                        
                                              
                                                                                 

                                                                       
                                                 
                                                                      
                                               
                                                             
                                                                           
                                                     
                                                                        
                                                             
                                  
              
                             
                                                                              
      
                                        
                                                                
                                                                                  
                                  
                                                                                            
                                                                             
                                                                                        
               
                                              
                                                           
             
          

                                                            
                                                                    
                                                             
                                                                           
                                                  
                                                              
                                                          
                                                 
                                                                               
                                                            
                                               
                                                                  
                                                                       
                                                
                                      
                                                                         
                                                    
                                                         

                                                                    
                                                                            
                                                                             
                                                                    
                                                             
                                                                                        
                                                                                          
                                                                                    
                                                                                          
                                                              
                                                               
                          
                                                                         
                                                    
                                                                                       
                 

end PositiveHighHeightEstimate
end QuadraticCarleson
