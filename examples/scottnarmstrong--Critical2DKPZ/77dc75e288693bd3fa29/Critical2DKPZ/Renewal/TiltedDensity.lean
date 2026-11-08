/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ScalarLaplace
public import Mathlib
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The exponentially tilted scalar renewal law

The Euler-shifted scalar density becomes a probability density after exponential
tilting above its critical abscissa. Its compactification has explicit moments.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.Renewal

/-- The exponentially damped positive-time scalar density, normalized to unit mass when the damping exceeds the critical abscissa. -/
def tiltedScalarDensity (θ a t : ℝ) : ℝ :=
  (Real.log a - θ) * (Real.exp (-(a * t)) * DeltaBose.scalarDensity θ t)

                                                       
                                                                                             
                            
                                                                                               
                                                                                      

                                                              
theorem tiltedScalarDensity_pos {θ a t : ℝ} (hθ : θ < Real.log a) (ht : 0 < t) :
    0 < tiltedScalarDensity θ a t :=
  mul_pos (sub_pos.mpr hθ) (mul_pos (Real.exp_pos _) (DeltaBose.scalarDensity_pos θ ht))

/-- The tilted scalar renewal density is integrable on positive times. -/
theorem integrableOn_tiltedScalarDensity (θ : ℝ) {a : ℝ} (ha : 0 < a) (hθ : θ < Real.log a) :
    IntegrableOn (tiltedScalarDensity θ a) (Ioi 0) :=
  (integrableOn_damped_scalarDensity θ ha hθ).const_mul _

/-- The normalized tilted scalar renewal density has total integral one. -/
theorem integral_tiltedScalarDensity (θ : ℝ) {a : ℝ} (ha : 0 < a) (hθ : θ < Real.log a) :
    (∫ t in Ioi 0, tiltedScalarDensity θ a t) = 1 := by
  unfold tiltedScalarDensity
  rw [integral_const_mul, integral_damped_scalarDensity θ ha hθ]
  exact mul_one_div_cancel (sub_pos.mpr hθ).ne'

/-- The scalar renewal law under exponential tilting, supported on strictly positive times. -/
def scalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a}) (hθ : θ < Real.log a) :
    ProbabilityMeasure ℝ :=
  ⟨(volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (tiltedScalarDensity θ a t)),
    ⟨by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
        ← ofReal_integral_eq_lintegral_ofReal (integrableOn_tiltedScalarDensity θ a.2 hθ)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact (tiltedScalarDensity_pos hθ ht).le),
        integral_tiltedScalarDensity θ a.2 hθ, ENNReal.ofReal_one]⟩⟩

                                                                 
                                                                            
                                                                       
                                                     

instance scalarRenewalLaw_noAtoms (θ : ℝ) (a : {a : ℝ // 0 < a}) (hθ : θ < Real.log a) :
    NullSingletonClass (scalarRenewalLaw θ a hθ : Measure ℝ) := by
  change NullSingletonClass ((volume.restrict (Ioi 0)).withDensity _)
  infer_instance

                                                                                                           
                                                                
                                       
                                                       
                                                         
                                                  
                                                                                          
                                                                   
                         
                                                              
                                                                            

                                                                 
                                             
                                            
                                                                

                                               
                                                                   
                       
          

                                                                                          
                                                 
                                                
                                            

                                                            
                                                                                  
                                         
                                              


                                                                        
                                                                           
                                   
                                                                                      
                                                     
                                                                
                                                                                 
                              
                                                                                
                                          
                                                                                  
      
                                        
                                                                           
                               
                                                   
                
                                                                     
                                                                                          
                                                       
                                
                                                               
                                               
                           
               
            
          
                                                                                
                                                  
                                 
               
                                                  
          

end Critical2DKPZ.Renewal

end
