/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Mathlib

/-!
# Definitions from the quadratic Carleson endpoint paper

This file records foundational objects from Sections 2 and 3 of the paper.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace QuadraticCarleson

                                                  
                                      
                                                       

       
                                      
              

                                                                                  
                                      
           
                                                  

       
                                                       

       
                                       
                                                            

                                                                           

                                                                          
                                                                              
structure YoungFunction where
  toFun : ℝ → ℝ
  continuousOn_nonneg : ContinuousOn toFun (Ici 0)
  convexOn_nonneg : ConvexOn ℝ (Ici 0) toFun
  strictMonoOn_nonneg : StrictMonoOn toFun (Ici 0)
  map_zero : toFun 0 = 0
  identity_or_superlinear :
    (∀ t ∈ Ici (0 : ℝ), toFun t = t) ∨
      Tendsto (fun t : ℝ => toFun t / t) atTop atTop

instance : CoeFun YoungFunction (fun _ => ℝ → ℝ) := ⟨YoungFunction.toFun⟩

                                                        
                                                         
                                                              

                                                                       
                            
structure L0Infinity where
  toFun : ℝ → ℂ
  measurable_toFun : Measurable toFun
  bounded_toFun : ∃ C : ℝ, ∀ x, ‖toFun x‖ ≤ C
  hasCompactSupport_toFun : HasCompactSupport toFun

instance : CoeFun L0Infinity (fun _ => ℝ → ℂ) := ⟨L0Infinity.toFun⟩

                                                                           
                   
                                       
                                                 
                                                                            

                                                                             
               
                                                                                     
                                                               
                                   

                                                            
                                          
                                     

                                                            
                                      
                                                                     

end QuadraticCarleson
