/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Basic
public import Mathlib
/-!
# Diagonal-dominance decay of finite-volume resolvents

If `|v x - z| ≥ N > K` on a finite volume `Λ`, where `K` bounds the row sums of the kernel `a`,
then `restrictedOp a v Λ - z • 1` is invertible and the resolvent column decays like
`(K / N) ^ ⌈d x y⌉₊ / (N - K)`, for every complex `z`.

The proof is by maximum propagation, with no
Neumann series.

Motivation: the base-scale mechanism of Fröhlich–Spencer (1983), Appendix A,
Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

                       
                                                                                              
                                                                                    
                                        
                                                                         
                                  
                                               
                     
                              
                  
                                                                     
                                                        
                                                       

                       
                                                                                  
                                                                                  
                                      
                                                                                          
                                                        
                               
                                                                                      
                                                     
           
                                                                                         
                                                                     
                                             
                                                            
                                                      
                       

                                                                            
theorem restrictedOp_sub_smul_mulVec_apply (v : X → ℝ) (Λ : Finset X) (z : ℂ) (u : X → ℂ) (x : Λ) :
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ (fun w : Λ => u w)) x =
      ((v x : ℂ) - z) * u x + ∑ w ∈ Λ, a x w * u w := by
  have e : ∀ w : Λ, (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) x w * u w =
      a x w * u w + (if x = w then ((v x : ℂ) - z) * u w else 0) := by
    intro w
    rw [Matrix.sub_apply, restrictedOp_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hxw : x = w
    · simp [hxw]
      ring
    · simp [hxw]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [add_comm, Finset.sum_coe_sort Λ fun w => a x w * u w]

                                                                                                
                                                            
                                         
                                                              
                                                              
                                           
                                                                 
                            
               
                                          
                                                             
                                                           
                                                                                 
                                                                            
                                                
                      
                                                                     
                                                                               
                             
                              
                                              
                                  
                                             
                      
                         
                                 
                    

                                                                                        
                                                                                   
theorem resolventColumn_row_of_isUnit (v : X → ℝ) (Λ : Finset X) {z : ℂ}
    (hU : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))) {y : X} (hy : y ∈ Λ) {x : X}
    (hx : x ∈ Λ) :
    ((v x : ℂ) - z) * resolventColumn a v Λ z y x +
      ∑ w ∈ Λ, a x w * resolventColumn a v Λ z y w = if x = y then 1 else 0 := by
  set M := restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) with hM
  have hcol : (fun w : Λ => resolventColumn a v Λ z y w) = M⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 := by
    funext w
    rw [Matrix.mulVec_single_one, resolventColumn_of_mem a v z w.2 hy]
    rfl
  have h2 : M *ᵥ (fun w : Λ => resolventColumn a v Λ z y w) = Pi.single ⟨y, hy⟩ 1 := by
    rw [hcol, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
  have h3 := congrFun h2 ⟨x, hx⟩
  rw [hM, restrictedOp_sub_smul_mulVec_apply] at h3
  rw [h3]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have : (⟨x, hx⟩ : Λ) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
    simp [this, hxy]

                                                                                                
                                                                                
                                                                                      
                                                                 
                                                                      
                                           
                                           
                                       
                                             
                              
      
                                                
                         
                                                                              
                                                       
                        
              
                          
                                            
                                                                            
                                                                   
                                                                                 
           
                    
             
                  
                                                                                  
                                                                                            
                                                                                        
                                 
                                    
                                                
                                                         
                            
                  
                   
                                                                                            
                                                          
                                                    
                             
                  
                          
                                                                                            
                                                                                 
                           
                        
                           
                                                  
                                                                                     
                                  
                                                                                    
                
                                                              
                                     
                                                                  
                   
                                             
                       
                    
                          

end FroehlichSpencer.Infra
