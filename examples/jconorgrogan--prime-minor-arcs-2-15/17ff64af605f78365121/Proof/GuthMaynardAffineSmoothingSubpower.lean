import GuthMaynardAffineSmoothingNorms

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Smoothing with a subpower-mass kernel

The bump in Guth--Maynard Lemma 9.2 is one-bounded but may have support and
mass `T^δ`.  It is therefore not a unit-mass kernel.  The Proposition 9.1
iteration needs the exact resulting loss, rather than the unit-mass closure
proved in `GuthMaynardAffineSmoothingNorms`.
-/

/-- A positive kernel whose mass is at most `K` enlarges a pointwise source
bound by at most the same factor. -/
theorem affineSmoothing_le_mass_mul
    {T S K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hf0 : ∀ u, 0 ≤ f u) (hf_le : ∀ u, f u ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hfCont : Continuous f) (x : ℝ) :
    affineSmoothing T psi f x ≤ K * S := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk : Integrable k := by
    simpa only [k] using
      (integrable_affineSmoothing_kernel hT hpsi).comp_sub_left x
  have hk0 : ∀ u, 0 ≤ k u := fun u => mul_nonneg hT.le (hpsi0 _)
  have hleft : Integrable (fun u => k u * f u) := by
    have hbound : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ S := by
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(neg_nonpos.mpr hS).trans (hf0 u), hf_le u⟩
    exact (hk.bdd_mul hfCont.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hright : Integrable (fun u => k u * S) := hk.mul_const S
  have hmono : (∫ u : ℝ, k u * f u) ≤ ∫ u : ℝ, k u * S := by
    apply integral_mono_ae hleft hright
    filter_upwards with u
    exact mul_le_mul_of_nonneg_left (hf_le u) (hk0 u)
  calc
    affineSmoothing T psi f x = ∫ u : ℝ, k u * f u := by rfl
    _ ≤ ∫ u : ℝ, k u * S := hmono
    _ = (∫ z : ℝ, psi z) * S := by
      rw [integral_mul_const, integral_affineSmoothing_kernel hT psi x]
    _ ≤ K * S := mul_le_mul_of_nonneg_right hmass hS

/-- The Fourier transform of a nonnegative kernel of mass at most `K` has
norm at most `K`. -/
theorem norm_fourier_ofReal_le_mass
    (psi : ℝ → ℝ) (hpsi0 : ∀ z, 0 ≤ psi z)
    {K : ℝ} (hmass : ∫ z : ℝ, psi z ≤ K) (xi : ℝ) :
    ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤ K := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (fun z : ℝ => (psi z : ℂ)) xi
  change ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤
    ∫ z : ℝ, ‖(psi z : ℂ)‖ at hraw
  have hnorm : (∫ z : ℝ, ‖(psi z : ℂ)‖) = ∫ z : ℝ, psi z := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpsi0 z)]
  rw [hnorm] at hraw
  exact hraw.trans hmass

                                                                     
                                                      
                                          
                        
                                
                                                 
                                          
                            
                                       
                                                    
                                                              

                                                                             
                                                         
                                          
                                                 
                                
                                               
                                               
                                              
                                    
                                                                 
                           
                                                                          
                                                    
                                                                  
                                                           
                                     
                                        
      
                                              
                                                        
                                      
            

                                                                        
                                                         
                                                    
                                            
                                         
                                
                                               
                                                       
                                     
                                                                
                           
                               
                                                                       
                  
                                             
                    
            
                                                                        
             
                                                                
                         
                                                        
              
      
                                                           
                                                                       
                                                 
                                                     
                                                        

                                                                             
                                                                             
                                                         
                                                    
                                                
                                          
                            
                                
                                            
                                                          
                                  
                                                 
                                     
        
                  
                   
                     
                                                                       
                                                                      
                                                           
                      
                        
           
                          
                         
           
                                                               
           
                                                                    
                                                        
              
                                                                          
                                             
             
                                                    
                       
                    
                         
                                                                     
                                                                        
                   

end GuthMaynardJIteration

                                                               
                                                               
                                                                                  
                                                                                     
                                                                                
                                                                                
