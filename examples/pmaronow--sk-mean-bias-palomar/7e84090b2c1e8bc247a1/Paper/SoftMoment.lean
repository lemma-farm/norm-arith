module
public import Paper.RSSoft
public import Paper.GaussianPoincare
public import Paper.Variational
public import Mathlib
@[expose] public section

/-!
# Actual soft Gaussian moment and the left-hand bound

The second moment is the literal squared Gaussian conditional `tanh`
expectation, evaluated at the Gaussian field at time `t`. Gaussian Poincaré
and the independent-sum law are proved in the imported modules. This file
assumes neither a Poincaré estimate nor the desired moment sign.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

/-- The actual Gaussian conditional second moment before the RS interface. -/
def softSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianExpectation (fun z => rsSoftDx β q t (gaussianField β h t z) ^ 2)

lemma soft_dx_square_norm_le_one (β q t x : ℝ) : ‖rsSoftDx β q t x ^ 2‖ ≤ 1 := by
  simpa only [norm_pow, one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_rsSoftDx_le_one β q t x) 2

/-- The soft Gaussian second moment is a genuine integrable expectation. -/
theorem integrable_softSecondMoment (β h q t : ℝ) :
    Integrable (fun z => rsSoftDx β q t (gaussianField β h t z) ^ 2) (gaussianReal 0 1) := by
  have hc : Continuous (fun z => rsSoftDx β q t (gaussianField β h t z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((hasDerivAt_rsSoftDx_spatial β q t _).continuousAt).comp
      (by unfold gaussianField; fun_prop)
  exact (integrable_const (1 : ℝ)).mono' (hc.pow 2).aestronglyMeasurable
    (.of_forall fun z => soft_dx_square_norm_le_one β q t _)

                                                                      
                                                              
                                             
                                                           
           
                                                                    
           
                                                                
                            
                            
                                                                        
                          
              
                                                            

                                                                                
                                                        
                                                     
                                                              

                                                    
                                                                        
                                           

                                                                       
lemma continuous_gaussian_average_fixed_scale (f : ℝ → ℝ) (a C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun x => gaussianExpectation (fun z => f (x + a * z))) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact .of_forall fun z => hb _
  · exact integrable_const C
  · filter_upwards [] with z
    exact hf.comp (by fun_prop)

lemma norm_gaussian_average_fixed_scale (f : ℝ → ℝ) (a x C : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ C) : ‖gaussianExpectation (fun z => f (x + a * z))‖ ≤ C := by
  simpa [gaussianExpectation] using norm_integral_le_of_norm_le_const
    (μ := gaussianReal 0 1) (f := fun z : ℝ => f (x + a * z)) (.of_forall fun z => hb _)

lemma integrable_nested_gaussian_field (f : ℝ → ℝ) (β h t a C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun z => gaussianExpectation (fun w => f (gaussianField β h t z + a * w)))
      (gaussianReal 0 1) := by
  have hc := (continuous_gaussian_average_fixed_scale f a C hf hb).comp
    (show Continuous (gaussianField β h t) by unfold gaussianField; fun_prop)
  exact (integrable_const C).mono' hc.aestronglyMeasurable
    (.of_forall fun z => norm_gaussian_average_fixed_scale f a _ C hb)

/-- The actual conditional Gaussian field composes to the terminal field. -/
theorem soft_gaussian_terminal_collapse (f : ℝ → ℝ) (β h q t C : ℝ)
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    gaussianExpectation (fun z => gaussianExpectation
      (fun w => f (gaussianField β h t z + β * Real.sqrt (q - t) * w))) =
      gaussianExpectation (fun z => f (gaussianField β h q z)) := by
  have heq : (fun z => gaussianExpectation
      (fun w => f (gaussianField β h t z + β * Real.sqrt (q - t) * w))) =
      (fun z => gaussianExpectation
        (fun w => f (h + β * Real.sqrt t * z + β * Real.sqrt (q - t) * w))) := by
    funext z
    congr 1
    funext w
    congr 1
    unfold gaussianField
    ring
  rw [heq, gaussianExpectation_double_affine_collapse h (β * Real.sqrt t)
    (β * Real.sqrt (q - t)) f hf.measurable C hb]
  have hvar : (β * Real.sqrt t) ^ 2 + (β * Real.sqrt (q - t)) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.1, Real.sq_sqrt (sub_nonneg.mpr ht.2)]
    ring
  rw [hvar, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]
  congr 1
  funext z
  congr 1
  unfold gaussianField
  ring

                                                                                
                                                     
                                           
                                                                                   
                                    
                                                       
                                                    
           
                                          
                          
                                               
           
                                                           
                              
                                                                                   
                                               
                                                 
                                                                              
                                               
                                                                                
                                                                  
                                                    
                                   
                                                        
                                                          
                                                                                            
                                                             
                                                                   
                                                                               
                                                               
                                                                          
                                                               
                                                          
                                                                                              
                                                          
                                                                          
                                      
                                          
             
                                                    
                   
                    
                   

                                                                                   
                                                     
                                                                           
                                                                    
                                                           
                      

                                                                                
                                                        
                                                                         
                                   
                                           
                                                                         
                                                                                             

                                                                                 
                                                
                                                                         
                                                                   
                                                                                     

end Paper
