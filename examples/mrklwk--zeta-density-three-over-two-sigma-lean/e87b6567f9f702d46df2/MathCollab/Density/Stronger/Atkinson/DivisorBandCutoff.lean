module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticDivisorBand
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


def zetaBandCutoff (a b c d x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a)) *
    Real.smoothTransition ((d - x) / (d - c))

                                                                               
                                                                              

                                                                                  
                                                                                        
                                                                                 

                                                                                        
                                                         
                                                       

                                                                         
                                                                    
                       
                                                                                              
                                                                                                     

                                                                 
                                                      
                       
                                          
                                                                                         

                                                                  
                                                      
                       
                                          
                                                                                         

                                                                          
                                                             
            
             
               
                                                               
               
                                                                

def zetaDivisorBandEdge (T G v : ℝ) : ℝ := T / (2 * Real.pi) * Real.exp (v / G)

def zetaDivisorBandCutoff (T G L : ℝ) : ℝ → ℝ :=
  zetaBandCutoff (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (-L))
    (zetaDivisorBandEdge T G L) (zetaDivisorBandEdge T G (2 * L))

                                                                
                                                                              

theorem zetaDivisorBandEdge_strictMono {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    StrictMono (zetaDivisorBandEdge T G) := by
  intro v w hvw
  unfold zetaDivisorBandEdge
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hG).mpr hvw))
    (by positivity)

                                                                          
                                                                    
                                           
                                                 
                                                           
                                                                             

                                                                           
                                                                   
                                                                                    
                                                 
                                                                    

                                                    
                                                                                 

end MathCollab.Density.Stronger.Atkinson
