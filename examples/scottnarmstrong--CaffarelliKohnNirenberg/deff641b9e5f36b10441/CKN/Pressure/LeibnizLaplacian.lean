-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import CKN.Foundation.Sobolev.Ambient.Basis
import CKN.Foundation.Sobolev.Measure.RestrictedVolume
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The Leibniz rule for the spatial Laplacian, in weak form

The paper's identity `eq:leibniz-lap`,
`Δ(η T) = η Δ T + 2 ∂_j η ∂_j T + T Δ η`,
is stated there for a scalar distribution `T` and a smooth `η`.  This file
proves the underlying pointwise second-order product rule for smooth functions
on `Vec3 := Fin 3 → ℝ`, and then integrates it against a locally integrable
weight to obtain the weak (test-function) form used in the paper.

Spatial partial derivatives are ordinary partial derivatives, expressed as the
Fréchet derivative applied to a coordinate basis vector, matching the
convention of `CKN.spatialPartial`.
-/

open MeasureTheory Set
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-! ## Spatial partial derivatives and their product rules -/

/-- The `i`th spatial partial derivative `∂_i f`, as the Fréchet derivative applied
to the `i`th coordinate basis vector. -/
def spatialDeriv (f : Vec3 → ℝ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => (fderiv ℝ f x) (basisVec i)

                                                   
                                                 
                                                           

                                                                  
                                                 
                                                               

                                               
                                                          
                                              

lemma contDiff_spatialDeriv_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f i) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (fderiv ℝ f x) (basisVec i)) := by
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      (contDiff_infty_iff_fderiv.mp hf).2
    have h := hfd.clm_apply (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 => basisVec i))
    simpa using h
  exact hcomp

                                                     
                                  
                                                  
                                               
                                                          
                            
                                                                         
         

                                                     
                                                               
                                                  
                                               
                                                              
                            
                                                                                  
         

                                                
                                                
                                              
                                                                    

                                                  
                                                                             
                                                                                         
                                                                                    
                            
                          
         

lemma spatialDeriv_mul {f g : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialDeriv (fun y => f y * g y) i x =
      spatialDeriv f i x * g x + f x * spatialDeriv g i x := by
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (fderiv_fun_mul hf hg)
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  simp only [spatialDeriv]
  rw [h]
  ring

                                                                               
                    
                                                      
                                                                                        
                                            
                               
                                               
                                               
                                       
                                                              
                                                              
                                                    
                                                                
                                                    
                                                                
                                               
                                                                          
            
                                            
                                                                       
                        
                                                                       
                        
                          
                                                                          
                                                            
                                                                 
                            
                                                                   
                                 
                                                    
                                       
                                                                   
                                               
                                      
                                       
                         
                             
                         
      

                                                                          
                                      
                                                    
                                                               
                                         
                                                                      
                                            
          
                                              
                                               
                                               
                                               
                                  
                                               
                                                                            
                                                       
                                                           
                                                                            

end

end CKN
