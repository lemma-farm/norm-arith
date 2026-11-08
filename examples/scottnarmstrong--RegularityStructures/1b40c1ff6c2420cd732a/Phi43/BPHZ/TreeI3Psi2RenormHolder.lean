/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusRenorm

/-!
# The renormalised convolution with Hölder increments

A variant of [Hai14, Lemma 10.16 (ii)] (`abs_integral_mul_sub_le`) in which the increment bound of
`f₂` is Hölder of exponent `lam ∈ (0, 1]`:
`|f₂(u + h) - f₂ u| ≤ B₂ s(h)^lam s(u)^(-a₂-lam)` for `s h ≤ s u / 2`.  If `f₁` has order `-a₁` with
`5 < a₁ < 5 + lam` and `f₂` order `-a₂`, then
`|∫ f₁(x) (f₂(z - x) - f₂ z) dx| ≤ C B₁ B₂ s(z)^(5-a₁-a₂)`.  This is needed for the difference of
renormalised convolutions, where `f₂` is a difference of kernels whose Hölder increments gain a
power of the distance between the scales by interpolation.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_mul_rpow_div_holder {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) (α β γ : ℝ)
    (h : α + β = γ) : ρ ^ α * (ρ / k) ^ β = k ^ (-β) * ρ ^ γ := by
  rw [Real.div_rpow hρ.le hk.le, Real.rpow_neg hk.le, ← h, Real.rpow_add hρ]
  field_simp

                                                                      
                                               
                                  

                                                                                     
theorem integral_renorm_majorant_near_holder {a₁ a₂ lam : ℝ} (hlam1 : lam ≤ 1)
    (ha₁ : 5 < a₁) (ha₁' : a₁ - lam < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ B : ℝ}, 0 < ρ → 0 ≤ B →
      Integrable (fun x => B * (2 ^ lam * ρ ^ (-a₂ - lam)) *
        singularLocalWeight (a₁ - lam) (ρ / 4) x) ∧
      ∫ x, B * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * K * ρ ^ (5 - a₁ - a₂) := by
  have hp : 0 < a₁ - lam := by linarith
  have h5 : 0 < 5 - (a₁ - lam) := by linarith
  refine ⟨2 ^ lam * (80 / (5 - (a₁ - lam)) * 4 ^ (-(5 - (a₁ - lam)))), by positivity, ?_⟩
  intro ρ B hρ hB
  have iL := integrable_singularLocalWeight hp ha₁' (by positivity : 0 < ρ / 4)
  refine ⟨iL.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := integral_singularLocalWeight_le hp ha₁' (by positivity : 0 < ρ / 4)
  have hc : 0 ≤ B * (2 ^ lam * ρ ^ (-a₂ - lam)) := by
    have := Real.rpow_nonneg hρ.le (-a₂ - lam)
    have h2 : (0 : ℝ) ≤ 2 ^ lam := Real.rpow_nonneg (by norm_num) _
    positivity
  have key := rpow_mul_rpow_div_holder hρ (by norm_num : (0 : ℝ) < 4) (-a₂ - lam)
    (5 - (a₁ - lam)) (5 - a₁ - a₂) (by ring)
  calc
    B * (2 ^ lam * ρ ^ (-a₂ - lam)) * ∫ x, singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * (2 ^ lam * ρ ^ (-a₂ - lam)) * (80 / (5 - (a₁ - lam)) * (ρ / 4) ^ (5 - (a₁ - lam))) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = B * 2 ^ lam * (80 / (5 - (a₁ - lam))) *
        (ρ ^ (-a₂ - lam) * (ρ / 4) ^ (5 - (a₁ - lam))) := by ring
    _ = _ := by rw [key]; ring

                                                                                                
                                                                                    
                                                                  
                                 
                                                                                      
                                                                                      
                                                         
                                                       
                                                                                                   
                                                                   
                                                                            
                                  
                                                                
                                                                       
                                                
                                                              
                                                      
                                                              
                                                       
                                                        
                                                                                     
                                       
                                               
                                                            
                                                   
                                                                      
                                                                 
                                                           
                                                     
                                                                     
                                                             
                                                                                        
                                                       
                                                 
                                                      
                                                                        
                                      
                                                                              
                                      
                                                                        
                                                           
                                      
              
                      
                                                                         
                                                                  
                                        
                                                    
                                           
                               
                                                          
                                                  
                                           
                                                                                    
                                                                  
                                                                                         
                                       
                                            
                                                                                              
          
                                      
                                                 
                                                                                   
                                                                    
                            
                                               
                                                                  
                                                   
                                                                                  
                                                           
            
               
                                                                                     
                                     
                                                                                           
          
                                                                                   
                                                                       
                                    
                                                
                                                     
                    
                                                                  
                                     
                                                                     
                                                                
                                                                  
                                                                         
                                                                         
                                                                       
                                                                  
                                                 
              
                                                                         
                                                            
                                                                            
                                                                               
                                                                          
                                    
                                        
                
                                                 
                                                                        
                                                                
                                                 
                                                     
                                                             
                                                                                 
                                                                 
                                                                 
                                                                     
                                                             
                                                           
                                                                    
                                             
                      
                                                                        
                                                  
                                                                   
                                       
                                                                      
                   
              
                                                                                              
                                                                   
                                                                                                   
                            
                
            

                                                                                                      
                                                                                         
                                                                               
                                                                             
                                                                                    
                                                                                    
                                                    
                                                         
                               
                                                                                   
                                                 
                                           
                                                                  
                                   
                                                                                          
                                                           
                                                                          
                                                              
                                             
                                       
                                             
                                                     
                                                                     
                             
                                             
                                             
                               
                                                                         
                                                    
                                                                           
                                                                          
                                                    
                                                               
                                                                                  
                                                                        
                                                    
                                                               
                                                                     
                                                                
                                                                
               
                                                                     
                                                                                        
                                                               
                                                                     
                                                                
                                                                  
                                                                                         
                   
                         
                                                                                         
                                                  
                                
                                                           
                                                    
                                                               
                                                                     
                                                                
                                                               
                                                                                               
                                                                    
                                                                          
                                                                   
                                                                  
                                                                      
                                                              
                                    
                                                                                   
                           
                                                                                            
                                          
                                                            
                                                             
                                          
                    
      
                                                  
                                                                                    
                                                       
                                                                                            
                                  

end RegularityStructures

end
