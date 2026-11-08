/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
public import DOZZ.GMC.AdmissibleCoarseBarrier
public import DOZZ.GMC.AdmissibleCoarseScaleBarrier
public import DOZZ.GMC.Construction.GMCBarrierCompactTestL1
public import DOZZ.GMC.Construction.FiniteGaussianWickPairTilt
public import DOZZ.GMC.GoodBarrierL2Cauchy
public import DOZZ.GMC.PowerKernelIntegrability

/-! Mixed-cutoff barrier estimates for compatible admissible logarithmic regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

                                                                                                
                                                                                                 
                                                                                                  
                                                                                          
                                   
                                                          
                         
                                                      
                                                      
                                                               
                  
                                                  
                                                                 
                                                                  
                                                                  
                              
                                                   
                                          
                                      
                                                      
                                     
                                                 
             
                                                                   
                                    
                                                                           
                                                      
                                
                                                                           
                                                      
                                                                     
                                      
                                              
                                                                                   
                                                                     
                                                           
                                                           
                                               
                                                           
                                                           
                                             
                                                
                               
              
              
                                                                               
                                                                                
                                                                                
                                                                                
                                                                                
                                                                                
                            
                                                     
                                       
                                              
              
                                         
                            
              
                                                                 
                                               
                           
                                                                                
                                     
              
                         
                                  
                                          
                                                                            
                                     
                                                                        
                                               
                    
           
               
                                   
                        
                        
                                                                         
                                                            
                                                                        
                             
                       
                                                      
                                            
                 
              
                                            
                                                    
                                                                             
                                                        
                                                   
                                 
                            
             
                                                                            
                                                        
                                                   
                                 
                            
                                              
                                            
                                                                  
              
            
                                                      
                                            
                 
              
                                                                                
                                                           
                                                        
                                                   
                                                              
                                                                                  
                                   
                             
                      
                            
             
                                                                                
                                                          
                                                        
                                                   
                                                              
                                                                                  
                                   
                             
                      
                            
                               
                                                               
                             
                           
                                        
                                                       
                                                    
                                                    
                                                       
                   
               
                     
                 
                                                                     
                                                            
                                                          
                                                              
                                       
                              
                  
                                                                     
                                                             
                                                          
                                                              
                                       
                              
                
                     
                 
                                                                     
                                                             
                                                          
                                                              
                                                                         
                              
                  
                                                                      
                                                             
                                                          
                                                              
                                       
                              
                                   
            
                                                   
                                                          
                                                                         
                                                                      
                                                                                      
            
                                                       


                                                                                              
                                                                                             
                                                                                   
theorem admissible_barrier_spatial_power_integrable
    (K : Set ℂ) (hK : IsCompact K) (f : ℂ → ℝ)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (B κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in K ×ˢ K,
        ENNReal.ofReal (B * f p.1 * f p.2 * ‖p.1 - p.2‖ ^ (-κ))
          ∂(volume.prod volume) ≤ C := by
  have hkernel := complex_norm_pair_neg_rpow_lintegral_isCompact K hK κ hκ hκ2
  obtain ⟨C₀, hC₀, hpair⟩ := hkernel
  let F : ℂ × ℂ → ℝ := fun p => B * f p.1 * f p.2
  have hFcont : Continuous F := by
    dsimp [F]
    exact continuous_const.mul (hf.comp continuous_fst) |>.mul (hf.comp continuous_snd)
  have hprod : IsCompact (K ×ˢ K) := hK.prod hK
  have habs : ContinuousOn (fun p : ℂ × ℂ => |F p|) (K ×ˢ K) :=
    hFcont.abs.continuousOn
  obtain ⟨R, hbound⟩ := hprod.bddAbove_image habs
  let R' : ℝ := max 0 R
  have hR' : 0 ≤ R' := le_max_left _ _
  have hFbound (p : ℂ × ℂ) (hp : p ∈ K ×ˢ K) : |F p| ≤ R' := by
    have hp' : |F p| ∈ (fun q : ℂ × ℂ => |F q|) '' (K ×ˢ K) := ⟨p, hp, rfl⟩
    exact (hbound hp').trans (le_max_right _ _)
  have hFnonneg (p : ℂ × ℂ) : 0 ≤ F p := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg hB (hf0 p.1)) (hf0 p.2)
  have hpoint (p : ℂ × ℂ) (hp : p ∈ K ×ˢ K) :
      ENNReal.ofReal (F p * ‖p.1 - p.2‖ ^ (-κ)) ≤
        ENNReal.ofReal R' * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) := by
    rw [← ENNReal.ofReal_mul hR']
    apply ENNReal.ofReal_le_ofReal
    calc
      F p * ‖p.1 - p.2‖ ^ (-κ) ≤ R' * ‖p.1 - p.2‖ ^ (-κ) :=
        mul_le_mul_of_nonneg_right (by
          have h := hFbound p hp
          rw [abs_of_nonneg (hFnonneg p)] at h
          exact h) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = R' * ‖p.1 - p.2‖ ^ (-κ) := rfl
  let J : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (F p * ‖p.1 - p.2‖ ^ (-κ))
  let G : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal R' * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ))
  have hJle : ∀ᵐ p : ℂ × ℂ ∂(volume.prod volume), p ∈ K ×ˢ K → J p ≤ G p := by
    filter_upwards [] with p
    intro hp
    exact hpoint p hp
  have hsing := setLIntegral_mono_ae' (hK.measurableSet.prod hK.measurableSet) hJle
  have hscale :
      (∫⁻ p in K ×ˢ K, G p ∂(volume.prod volume)) ≤ ENNReal.ofReal R' * C₀ := by
    calc
      _ = ENNReal.ofReal R' *
          (∫⁻ p in K ×ˢ K,
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volume.prod volume)) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal R' * C₀ := by
        simpa [mul_comm] using mul_le_mul_left hpair (ENNReal.ofReal R')
  refine ⟨ENNReal.ofReal R' * C₀, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀, ?_⟩
  calc
    _ = ∫⁻ p in K ×ˢ K, J p ∂(volume.prod volume) := by
      apply setLIntegral_congr_fun (hK.measurableSet.prod hK.measurableSet)
      intro p hp
      rfl
    _ ≤ ∫⁻ p in K ×ˢ K, G p ∂(volume.prod volume) := hsing
    _ ≤ ENNReal.ofReal R' * C₀ := hscale

                                                                                            
                                                                                              
                                                              
                                                              
                                              
                                            
                                                               
                                             
                              
                                                                   
                       
                                                     
                                       
                            
                                                                           
                                       
                                                           
                                        
                                                           
                                                                     
        
                                            
                                          
                                                      
                                 
                                                                    
                        
                                                         
                                        
                        
               
            
             
                                                     
                               
                                                  
                                
                                             
                                                            
                        
                                                 
                                                          
                                                                
                        
           
                       
                                      
                     
                                
                       
                       
                                                           

                                                                                     
                                                                                         
                                                                                               
                                
                                                                         
                                   
                                                          
                         
                                                      
                                                      
                                                               
                  
                                                
                                                     
                                                   
                                     
                                         
                                     
                                      
                                                        
                                                               
                                                        
                                     
                      
                                                             
                                                       
                                      
                    
                                      
                                                   
                                                                     
                           
                                                     
                                           
                                                                                   
                                                              
                                      
                                                                                   
                                                              
                                                                             
                                           
                                              
                                                                                                                 
                                               
                                                                        
                    
                          
                                  
                                  
                                                                           
                                                      
                              
                                                                           
                                                      
                                                                     
                                  
                                    
                                                    
                                             
                                                                        
              
                      
                                                                  
                                                   
                                                          
                         
                                                                                 
                                             
                                         



end DOZZ.Proofs
