/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelField
public import RegularityStructures.Abstract.Datum.HeatField

/-!
# Spatial derivatives of the Duhamel field

For `g` smooth and spatially periodic, `∂_j (duhamelField g) = duhamelField (∂_j g)` on `{t > 0}`
(`pd_succ_duhamelField`): the spatial derivative falls on the forcing
(`hasTorusDeriv_duhamel`).  Iterating, every spatial derivative of the Duhamel field is the
Duhamel field of the corresponding derivative of the forcing (`pdWord_duhamelField`), and so is
bounded by `t` times the corresponding sup norm of the derivative of the forcing
(`abs_duhamelField_le`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE

                                                                                                
                
                                                                    
                                         

variable {g : ParabolicSpace → ℝ}

                                                                                              
                                                                                
                       
                                                               
                        
                                                                      
              
                                
                                                                                         
                 
                                 
                                                                                   
                   

                                                  
                                                                             
                                                                                                              
                                                                   
                                                                    
                                                                                 

                                                  
                                                                 
                               

                                                                            
                                                                                      
                    

                                                                               
                                                                           
                                                                   
                                                                   

                                                              
                                                                                               
                                                           
       
                                           
                                                                                     
                    

                                                            
                                                        
         
                                                                             
                                          
            
                                                                          
                                                    
                                                     
                                          
                                               
                                                        
                                                                               
                            
                                                     
                                                                              
                                                                                             
           
            
                       
                                                                                     
       
        
         

                                                                                                  
                
                                                                                                 
                                                                              
                                                              
                                                                   
                                                                                               
                                                   
                                                               
                                                            
                                              
                                    
                                                                  
                                                                                       
                                                   
                                         
                                                                
                                                                       
                               
                                                                    
                     

                                                                                              
                                                                     
              
                                                      

                                             
                                                            
            
                                                

                                                                                                 
             
                                                                                      
                    
                                                                           
                                 
              
                  
                                                         
                                                                   
                                                                  
                                                       
                                       
               
                                                 

theorem norm_forcePath_le (hg : PerSmooth g) {t M : ℝ}
    (hM : ∀ s ∈ Set.Icc 0 t, ∀ y, |g (s, y)| ≤ M) (ht : 0 ≤ t) :
    ∀ s ∈ Set.Icc 0 t, ‖forcePath hg s‖ ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ⟨ht, le_rfl⟩ 0)
  intro s hs
  refine (ContinuousMap.norm_le _ hM0).2 fun x => ?_
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [forcePath_apply, Real.norm_eq_abs]
  exact hM s hs y

/-- **Sup bound of the Duhamel field**: `|duhamelField g (t, y)| ≤ M t` if `|g| ≤ M` on
`[0, t] × ℝ³`. -/
theorem abs_duhamelField_le (hg : PerSmooth g) {t M : ℝ}
    (hM : ∀ s ∈ Set.Icc 0 t, ∀ y, |g (s, y)| ≤ M) (ht : 0 < t) (y : Fin 3 → ℝ) :
    |duhamelField hg (t, y)| ≤ M * t := by
  rw [duhamelField_of_pos hg ht]
  have h := norm_duhamel_le_mul (continuous_forcePath hg) ht.le (norm_forcePath_le hg hM ht.le)
  exact (Real.norm_eq_abs _ ▸ (ContinuousMap.norm_coe_le_norm _ (torusProj y))).trans h

end RegularityStructures.Inhomogeneity
