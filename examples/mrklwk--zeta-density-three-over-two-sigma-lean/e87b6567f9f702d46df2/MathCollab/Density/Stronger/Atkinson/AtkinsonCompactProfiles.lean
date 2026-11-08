module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightSmooth
public import MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeRescaled
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaMainMellinProfile (u : ℝ) : ℂ :=
  zetaDivisorWeight ((Real.log u + Real.log (2 * Real.pi) : ℝ) +
    (Real.pi / 2 : ℝ) * I)

theorem contDiffAt_zetaMainMellinProfile {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 1 zetaMainMellinProfile u := by
  have hl : ContDiffAt ℝ 1 Real.log u := Real.contDiffAt_log.mpr hu.ne'
  have hc : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hw : ContDiff ℝ 1 zetaDivisorWeight := contDiff_zetaDivisorWeight.of_le (by simp)
  unfold zetaMainMellinProfile
  fun_prop

                                                                                 
                                                                  
                                         
                                                  
                                                                                        
         
           
      

theorem exists_intervalC1Bound_zetaMainMellinProfile :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      IntervalC1Bound (fun x => zetaMainMellinProfile (x / T)) (T / 16) T C :=
  exists_intervalC1Bound_rescaled (fun _ hu => contDiffAt_zetaMainMellinProfile hu)

                                         
                                                

                                                                      
                                                   
                                                
                                                          
                                    
                             
                                                                

                                                                 
                    
                                                                                   
                                    
            
                                        
                                             
                                                                                                
                                                                                
                                                   
                                

end MathCollab.Density.Stronger.Atkinson
