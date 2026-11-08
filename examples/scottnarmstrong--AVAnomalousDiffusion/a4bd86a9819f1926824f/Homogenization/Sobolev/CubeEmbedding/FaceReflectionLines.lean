-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib

@[expose] public section

namespace Homogenization

open Homogenization
open scoped BigOperators

/-!
# Single-face even reflection: definitions and per-line calculus

Global (on all of `ℝ^d`) even reflection of a function across the face
`{x_i = a}`, its candidate gradient (sign-flipped in direction `i` on the
reflected side), the geometric fact that the reflection commutes with coordinate
insertion, and the one-dimensional derivatives of the direct and reflected line
functions.  These feed the Fubini assembly in `FaceReflection`.
-/

noncomputable section

variable {d : ℕ}

                                                                       
                                  
                                                                  
                                                                 

                                                                                  
                                                                      
                                                                   
            
                                               
                                          
                                                           

                                                                                 
                                                              
                                                                       
                         
                                                                               
          
                                
                                
                 
                                                
                                           

                                                                                     
theorem hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => (i.insertNth t z : Vec (n + 1))) (basisVec i) t₀ := by
  have hfun : (fun t : ℝ => (i.insertNth t z : Vec (n + 1)))
      = fun t => t • (basisVec i) + i.insertNth 0 z := by
    funext t
    funext j
    rcases eq_or_ne j i with h | h
    · subst h
      simp [Fin.insertNth_apply_same, basisVec]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simp [Fin.insertNth_apply_succAbove, basisVec, Fin.succAbove_ne]
  rw [hfun]
  simpa using ((hasDerivAt_id t₀).smul_const (basisVec i)).add_const (i.insertNth 0 z)

                                                                          
                 
                                                                      
                          
                                                                   
                            
                                                                 
                                                    
                                                                       
                    

                                                                               
                                                               
                                                                      
                                             
                                                          
                                                                                      

                                                                        
                                                                       
                                                                              
                                                       
                                                                     
                                                                  
                                           

                                                                                  
                                                                           
                                                             
                                                        
                                                                    
                                                                   
                           
                                                                        
                                                    
                      
                                                          
                                                  
                                                                  
                                                                     
                                                                   
                 
                                                    

                                                                         
                                 
                                                                                   
                                                                       
                          
                                                                       
                                                                                    
                                                                                  
                                                         

end

end Homogenization
