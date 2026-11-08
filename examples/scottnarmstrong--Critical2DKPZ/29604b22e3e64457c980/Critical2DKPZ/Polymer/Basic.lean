/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.PointToPoint
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Definitions.ProfileP2Fun
public import Critical2DKPZ.Definitions.SmoothedP2Plane
public import Critical2DKPZ.Definitions.SrwKernel
import Mathlib.Tactic

/-! Finite polymer path weights include disorder at times `a+1,…,a+n`, as in equation (1.3), and yield measurable partition functions supported on reachable endpoints. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The Boltzmann weight of a fixed walk, excluding its initial disorder slice. -/
def pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) : ℝ :=
  Real.exp (∑ j ∈ Finset.Icc 1 n,
    (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2))

/-- A site is reachable when an `n`-step nearest-neighbour path from the starting site ends there. -/
def Reachable (n : ℕ) (w z : Site) : Prop :=
  ∃ s : Fin n → Fin 4, walkPosition w s n = z

                                                    
                                                         
                                        
                               
                


                                             
                                                                
                         
                                         
                   
          

                                                                               
theorem pointToPlane_eq_sum (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β a n w ω =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω := rfl

/-- The point-to-point partition function is a finite sum of endpoint-constrained weighted paths. -/
theorem pointToPoint_eq_sum (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        if walkPosition w s n = z then 1 else 0 := rfl

                                                                  
                                                                      
                                    
                          
                                                                               
                        

                                                            
                                                                           
                                      
                          
                                               
                                                              
                                 

                                                                                        
                                                                            
                                                        
                          
                                                         
                                                              
                                   
               
                       
                    
                 
                                                                   
                    
                                     
                                    
                                                          

                                                                                       
                                                                                
                                                          
             
               
                                                      
                 
                          
            
                                             
                                                   
                                       

                                                                                                 
                                                      
                                 
                                                           
                                               
                                       
             
                                
                   
                                                                    


                                                           
                                                              
                                           
                     
          


                                                           
                                                                
                                             
                     
          

                                                           
       
                                                                  
                                
                     

                                                                 
                                                   
                                 
                                                           
                                     

                                                                                  
theorem walkPosition_eq_start_add {n : ℕ} (w : Site)
    (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition w s j = w + walkPosition 0 s j := by
  simp only [walkPosition, zero_add]

                                             
       
                                                  
                                        
                                  
                   

                                                                     
       
                                                                     
                                    
                            

                                                                                     
       
                                                                       
                                                           
                            

end Critical2DKPZ.Polymer
