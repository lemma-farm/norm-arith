/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Mild
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Smooth nonlinearities and their jets

A nonlinearity `G : ℝ × T³ × F → F` is smooth when its lift
`nonlinLift G (s, y, v) = G(s, torusProj y, v)` is smooth on `ℝ × ℝ³ × F`. Its derivative in
`(x, u)` descends to a continuous map `nonlinDeriv G` on `ℝ × T³ × F`.

* `hasTorusDeriv_nemytskii`: the chain rule for `x ↦ G(s, x, v(x))`;
* `jetNonlin G`: the nonlinearity `(s, x, v, ω) ↦ (G(s, x, v), (D G(s, x, v)(eᵢ, ωᵢ))ᵢ)` of the
  system satisfied by a solution together with its first partial derivatives;
* `contDiff_nonlinLift_jetNonlin`: the jet nonlinearity of a smooth nonlinearity is smooth.
-/

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

                                                                                     
                                                                          
                                 

                                                                                              
                                                             
                                                              
                                                                             
                              
                                           
                        
                                                                                            
                                                                     
                                                                            
                                        
                               
                               
            
                              

                                                                    
                                                                    
                                
                                                                                  

end RegularityStructures.PDE

end

public section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

                         
                                                                                      
                            
                                                                                      
          
                                      

                                                                                         
                                                                                                   
                                                                     
                                                                               
                                         
                                                    
                                                                               
        
              
                          

                                                                                            
                               
                                                              

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                                              
                                                                               
                                                   
                                                  
                                                         

                                                                                              
                                                                                         
                                                                             
                                                            
                                      
                                                                               
                        
                                                                                              
              
                                                                    
                                                                                                   

                                                                                           
                                                                                        
                                                                            
                                                                      
                                    
                                                                      
                                              

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial derivatives of a `C¹` function on `T³`, descended from its periodic lift. -/
def torusDerivOf (g : C(Torus3, F)) (hg : ContDiff ℝ 1 fun y => g (torusProj y)) :
    C(Torus3, Fin 3 → F) :=
  torusDescend (fun y i => fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1))
    (continuous_pi fun _ => (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    fun _ _ hab => funext fun _ => by rw [fderiv_lift_eq_of_torusProj_eq hab]

end RegularityStructures.PDE

end

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                                           
                                     
                                                                   
                                                       

                                                                        
                                                                                            
                                     
                                                                      
                                                         
                            
                                                                                       
                                                 
                                                                                   
                                                               
                                                               
                         

                                                                                      
                                                      
                                                                             
                     
                                                                                
                                         
                                   
         
       
                                       
                          
                     
        

                                                                                     
                                                                            
                                                                                             
                                                                                      
                                                                      
         
                                                                   
                                                                                        
                                    
                                                                        
                                                                    
                                                               
                                                                                           
                                              
                                                                       
                                   
                                     
          
          

theorem torusDerivOf_torusProj (g : C(Torus3, F)) (hg : ContDiff ℝ 1 fun y => g (torusProj y))
    (y : Fin 3 → ℝ) (i : Fin 3) :
    torusDerivOf g hg (torusProj y) i = fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1) := by
  simp [torusDerivOf]

theorem hasTorusDeriv_torusDerivOf (g : C(Torus3, F))
    (hg : ContDiff ℝ 1 fun y => g (torusProj y)) : HasTorusDeriv g (torusDerivOf g hg) := by
  intro y
  have : ofPartials (torusDerivOf g hg (torusProj y)) = fderiv ℝ (fun y => g (torusProj y)) y := by
    rw [← ofPartials_apply_single (fderiv ℝ (fun y => g (torusProj y)) y)]
    congr 1
    funext i
    exact torusDerivOf_torusProj g hg y i
  rw [this]
  exact (hg.differentiable one_ne_zero y).hasFDerivAt

open scoped ContDiff in
theorem contDiff_torusDerivOf_lift {g : C(Torus3, F)}
    (hg : ContDiff ℝ ∞ fun y => g (torusProj y)) :
    ContDiff ℝ ∞ fun y => torusDerivOf g (hg.of_le (by exact_mod_cast le_top)) (torusProj y) := by
  have h : (fun y => torusDerivOf g (hg.of_le (by exact_mod_cast le_top)) (torusProj y)) =
      fun y i => fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1) := by
    funext y i
    exact torusDerivOf_torusProj _ _ y i
  rw [h]
  exact contDiff_pi.2 fun i =>
    (hg.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const

                                                                                            
                                                        
                                                                                          
                                                                                
                                
          
                                                                                

                       
                                                               
                                                                
                                        
                                                   
                                                                
                           
                                                                                                
                                                                
                                                           
                                                        
                                         
                                                                        
                                                     
                                                                                       

                                                                 
                                                                                             
                                               
                                                                
                                                          
                                                                         
                                                            
                                                                          
                                     
                                                                                        
                                      
                                                                      
                                                                        
                                            
                          

end RegularityStructures.PDE

end
