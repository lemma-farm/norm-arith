/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.PVFourier
import QuadraticCarleson.QuadraticKernelLimit

/-!
# Quadratic Carleson operators on Schwartz functions

The singular integral in the paper is unambiguous on Schwartz functions when
defined by pairing the quadratically modulated principal-value tempered
distribution with `y ↦ f (x - y)`.  This file defines that action and proves
that it is exactly the limit of the paper's symmetric truncations.  It then
defines the full and lacunary pointwise suprema.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson

/-- The Schwartz test function `y ↦ f (x - y)` occurring in convolution with
the principal-value kernel. -/
noncomputable def schwartzFlipTranslate (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  (schwartzReflection f).compSubConstCLM ℂ x

@[simp]
theorem schwartzFlipTranslate_apply (f : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    schwartzFlipTranslate f x y = f (x - y) := by
  simp [schwartzFlipTranslate, schwartzReflection_apply]

/-- The paper's fixed-modulation quadratic Hilbert transform, defined
canonically by the tempered distribution `e(λy²) · p.v. (1/y)`. -/
noncomputable def quadraticHilbertSchwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  quadraticKernelDistribution modulation (schwartzFlipTranslate f x)

/-- The distributional action has exactly the paper's symmetrically truncated
integrals before passage to the principal-value limit. -/
theorem quadraticKernelTruncationAction_flipTranslate
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticKernelTruncationAction modulation ε (schwartzFlipTranslate f x) =
      quadraticHilbertTrunc modulation ε f x := by
  rw [quadraticKernelTruncationAction_eq_integral]
  unfold quadraticHilbertTrunc
  apply integral_congr_ae
  filter_upwards with y
  simp only [schwartzFlipTranslate_apply]
  ring

/-- On every Schwartz function, the canonical distributional definition is
the ordinary symmetric principal value stated in the paper. -/
theorem hasQuadraticPrincipalValue_schwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasQuadraticPrincipalValue modulation f x
      (quadraticHilbertSchwartz modulation f x) := by
  unfold HasQuadraticPrincipalValue
  simpa only [quadraticKernelTruncationAction_flipTranslate,
    quadraticHilbertSchwartz] using
      tendsto_quadraticKernelTruncationAction modulation (schwartzFlipTranslate f x)

                                                                      
                                                 
             

                                                                   
                                

                                                                             
                                                                                
                                                                           
                                                                            

                                                                           
                                                   
                                   
                         
                                                       

                                                             
                                            
                                                              
                                      
                                                                                  

                                                                     
                                   
                                                                        
                                              
                      
                                                                         

                                                                         
                                            
                           
                                                                               
               
         
                                                             
                            

end QuadraticCarleson
