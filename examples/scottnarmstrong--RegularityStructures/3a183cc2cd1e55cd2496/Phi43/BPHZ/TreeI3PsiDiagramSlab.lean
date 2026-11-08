/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagram

/-!
# The diagram bound for `I(Ψ³)Ψ` without a time support hypothesis on `Q`

`i3PsiPairing_bound` assumes that the covariance `Q` vanishes for `|t| > 2`.  The mollified
covariance `Q_ε = K_ε ⋆ K_ε^-` is supported in `|t| ≤ 2 (1 + ε² R)` where `R` is the time radius of the
mollifier, so this fails for every `ε > 0` as soon as `R > 0`.  The support is used only to bound
`Q(w - v)²` by `3^δ s(w - v)^(-2-δ)`; but the recentred kernels `δK(z, w)`, `δK(z', v)` vanish unless
`|w.1|, |v.1| ≤ 2` (for `s(z), s(z') ≤ 1`), hence only `|(w - v).1| ≤ 4` matters, where `s ≤ 3` still
holds.  This file re-proves the chain and total bounds with the support hypothesis on `Q` removed
(the support hypothesis on `K` is kept).

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- On the slab `|t| ≤ 4` the parabolic size is at most `3`. -/
theorem torusParabolicSize_le_three_of_abs_le_four {w : SpaceTime} (hw : |w.1| ≤ 4) :
    torusParabolicSize w ≤ 3 := by
  have h1 : √|w.1| ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have h2 := torusSpatialNorm_le_seven_eighth w.2
  unfold torusParabolicSize
  linarith

/-- The covariance squared, with a loss `δ` of the exponent, on the slab `|t| ≤ 4`. -/
theorem abs_Q_sq_le_of_abs_le_four {Q : SpaceTime → ℝ} {B δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {x : SpaceTime} (hx : 0 < torusParabolicSize x) (hx4 : |x.1| ≤ 4) :
    |Q x| ^ 2 ≤ B ^ 2 * 3 ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
  have h3 := torusParabolicSize_le_three_of_abs_le_four hx4
  have h1 := hQ x hx
  have hsq : |Q x| ^ 2 ≤ (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e : (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 =
      B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize x ^ (-(1 : ℝ))) 2,
      ← Real.rpow_mul hx.le]
    norm_num
  have hpow : torusParabolicSize x ^ (-(2 : ℝ)) =
      torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hle : torusParabolicSize x ^ δ ≤ 3 ^ δ := Real.rpow_le_rpow hx.le h3 hδ
  have hnn : 0 ≤ torusParabolicSize x ^ (-(2 + δ)) := Real.rpow_nonneg hx.le _
  calc |Q x| ^ 2 ≤ B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := hsq.trans e.le
    _ = B ^ 2 * (torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      rw [hpow]
    _ ≤ B ^ 2 * (3 ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      exact mul_le_mul_of_nonneg_right hle hnn
    _ = _ := by ring

                                                                                      
                                                                                        
                                                                                        
                                                
                                                                                        
                                                                                                   
                                                                               
                                         
                                                                                  
                                                                                    
                                    
                                                                                            
                                                                            
                                         
                                                               
                                                                                   
                                                                                               
                                       
                                                                                  
                                                                    
                                                               
                                                   
                                                                                       
                                                           
                         
                           
                                       
                                           
                 
                                               
                                               
                                              
                                                                          
                         
                                    
            
                                                 
                                                             
                                                         
                                                                         
                                                     
                                                                    
                                                                                       
                                                        
                                                                                                    
                                                                
                                                                             
                                                                            
                                 
                                                                                       
                                                                   
                                                                                  
                                           
                                    
          
                                                                                   
                                                      
                         
                 
            
                       
                
                                                                               
                                                    
                       
               
          
                     
              

                                                                                            
                                                                            
                                                                                        
                                                            
                                                                                       
                                                             
                                                                                       
                                                                
                                                                                       
                                 
                                               
                                                                                     
                                                  
                                                                                 
                                               
                                                       
                                                        
                                                               
                                    
                                                              
                                             
                                                                       
                                                              
                                                                
                                                                  
                                                 
                                                   
                                                  
                                           
                                                                                        
                                               
                          
                                                       
                                                      
                                                      
                                                      
                                                       
                                                      
                      
                                              
                                         
                                    
                     
                              
                                             
                                    
                              
                     
                                                                            
                                                                             
                                                                                            
                   
                                           
                          
                      
                               
                                           
                              
                               
                               
                          
                                                                                               
                                                                                               
                                                                                               
                                                                                               
                             
            
                                                                            
                                                                                              
                            
                   
                                                                                          
                                                    
                                              
                                                      
                                                       
                                              
                                                      
                                                       
                                                                                          
                                                       
                                                                           
                                                                                        
                                                                  
                                                          
                  
                                                                                                   
                     
            
                                                          
                                                                           
                                                                          
                                       
                                                                                      
                                                    
                                               
                                           
                                                                           
                                                                          
                                  
                                                                           
                                                                  
                                            
                                                                                      
                                                    
                                   
                                                                                       
                                                                      
                                                               
                           
                                            
                                                                
                                      
                                                                           
                                                                          
                                      
                                                                                     
                                                   
                                                                                      
                                                                                           
                                                                                
                                   
        
                                                    
                                                  
                                              
                                                     
          
                      
      

end RegularityStructures

end
