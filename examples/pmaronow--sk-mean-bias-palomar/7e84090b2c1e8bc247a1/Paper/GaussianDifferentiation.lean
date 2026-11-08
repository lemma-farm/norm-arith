module
public import Paper.Gaussian
public import Mathlib

@[expose] public section

/-!
# Differentiating concrete Gaussian expectations in the external field

Derivative exchange is proved by dominated differentiation against the standard
Gaussian probability measure. No Gaussian integration-by-parts or heat-equation
identity is assumed in these field-derivative results.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

 theorem gaussian_continuous_sech : Continuous sech :=
  continuous_const.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))

 theorem gaussian_continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)

/-- A reusable, genuinely proved dominated-differentiation theorem. -/
theorem hasDerivAt_gaussian_shift (f df : ℝ → ℝ) (a h M : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hi : Integrable (fun z => f (h + a * z)) (gaussianReal 0 1))
    (hd : ∀ x, HasDerivAt f (df x) x) (hb : ∀ x, ‖df x‖ ≤ M) :
    HasDerivAt (fun b => gaussianExpectation (fun z => f (b + a * z)))
      (gaussianExpectation (fun z => df (h + a * z))) h := by
  have hc (b : ℝ) : Continuous (fun z : ℝ => b + a * z) := by fun_prop
  have hmeas : ∀ᶠ b in 𝓝 h,
      AEStronglyMeasurable (fun z => f (b + a * z)) (gaussianReal 0 1) :=
    .of_forall (fun b => (hf.comp (hc b)).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable (fun z => df (h + a * z)) (gaussianReal 0 1) :=
    (hdf.comp (hc h)).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ), ‖df (b + a * z)‖ ≤ M :=
    .of_forall (fun z b _ => hb _)
  have hdiff : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun x => f (x + a * z)) (df (b + a * z)) b := by
    filter_upwards [] with z b _
    exact (hd (b + a * z)).comp_add_const b (a * z)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b z => f (b + a * z)) (F' := fun b z => df (b + a * z))
    (bound := fun _ => M) (s := Set.univ) (by simp)
    hmeas hi hmeas' hbound (integrable_const M) hdiff).2

                                            
                                                                                                 

                                            
                                                                                                 

 theorem sech_sq_derivative_bound (x : ℝ) :
    ‖-2 * Real.tanh x * sech x ^ 2‖ ≤ 2 := by
  have he : ‖-2 * Real.tanh x * sech x ^ 2‖ = 2 * |Real.tanh x| * sech x ^ 2 := by
    simp only [norm_mul, norm_neg, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg (sech x))]
    norm_num
  rw [he]
  have hm := mul_le_mul (Real.abs_tanh_lt_one x).le (sech_sq_le_one x)
    (sq_nonneg (sech x)) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

                                               
                                             
                                                                                  
                                                    
                                                     
            
         
                                                                          
                                                              
           

                                                                              
                                              
                                                                    
                                                            
                                                              
                                                                                                                           
                                                                                                
                                                                                            
                          
                                                                                
                                                                
                    
                              
                             
                           
                            
        
               
          

                                                                              
                                              
                                                                    
                                                            
                                                              
                                                                                                                           
                                                                                                        
                                                                                            
                          
                                                                                
                                                                
                    
                              
                             
                           
                            
        
               
          

                                                    
                                                                                                 
                                                            
                                                           
         
                                            
        

end Paper
