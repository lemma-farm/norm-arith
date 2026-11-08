/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.FiniteGreen
public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.APriori
public import FroehlichSpencer.Infra.Green.PathExpansion
public import Mathlib
/-!
# "`v = +∞` outside `Λ`" as a resolvent limit
-/

@[expose] public section

open Filter Topology Matrix

namespace FroehlichSpencer.T12

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}

                                                                                
                                                                                  
                                                      
                                                          
                                                              
                                                                        
                                                      
                                                            
                                                  
                                                                               
                                                                       

                                                                              
                                                                                      
                       
                                                                                
                                                                     
           
                                        
                        
                              
                
                              
        

                                                          
                                                                                 
theorem resolventColumn_eq_sub_sum_coupling_of_mem (ha : ∀ x y, a y x = star (a x y))
    (v : X → ℝ) {A B : Finset X} (hBA : B ⊆ A) {z : ℂ} (hz : z.im ≠ 0) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) :
    Infra.resolventColumn a v A z y x =
      Infra.resolventColumn a v B z y x -
        ∑ k ∈ B, ∑ k' ∈ A \ B, Infra.resolventColumn a v B z k x * a k k' *
          Infra.resolventColumn a v A z y k' := by
  have hA : IsUnit (Infra.restrictedOp a v A - z • (1 : Matrix A A ℂ)) :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp ha v A) z hz
  have hB : IsUnit (Infra.restrictedOp a v B - z • (1 : Matrix B B ℂ)) :=
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp ha v B) z hz
  set g := Infra.resolventColumn a v A z y with hg
  set M := Infra.restrictedOp a v B - z • (1 : Matrix B B ℂ) with hM
  let r : B → ℂ := fun u => ∑ k' ∈ A \ B, a u k' * g k'
  have hMg : M *ᵥ (fun w : B => g w) = Pi.single ⟨y, hy⟩ 1 - r := by
    funext u
    have hrow := Infra.resolventColumn_row_of_isUnit (a := a) v A hA (hBA hy) (hBA u.2)
    rw [← Finset.sum_sdiff hBA (f := fun w => a u w * g w)] at hrow
    rw [hM, Infra.restrictedOp_sub_smul_mulVec_apply]
    simp only [r, Pi.sub_apply, Pi.single_apply, Subtype.ext_iff]
    rw [← hg] at hrow
    linear_combination hrow
  have hgB : (fun w : B => g w) =
      M⁻¹ *ᵥ Pi.single ⟨y, hy⟩ 1 - M⁻¹ *ᵥ r := by
    rw [← Matrix.mulVec_sub, ← hMg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), Matrix.one_mulVec]
  have h1 := congrFun hgB ⟨x, hx⟩
  rw [Pi.sub_apply, Matrix.mulVec_single_one] at h1
  simp only [Matrix.mulVec, dotProduct] at h1
  change g x = _ at h1
  have e : ∀ k ∈ B, ∑ k' ∈ A \ B, Infra.resolventColumn a v B z k x * a k k' * g k' =
      Infra.resolventColumn a v B z k x * ∑ k' ∈ A \ B, a k k' * g k' := fun k _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl e, h1, ← Finset.sum_coe_sort B]
  congr 1
  · rw [Infra.resolventColumn_of_mem a v z hx hy]; rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Infra.resolventColumn_of_mem a v z hx k.2]

/-- Bridge `finiteGreen` to `resolventColumn`. -/
theorem finiteGreen_eq_resolventColumn {ν : ℕ} (B : Finset (Site ν)) (v : Site ν → ℝ)
    (E ε : ℝ) (hε : ε ≠ 0) (x y : {x // x ∈ B}) :
    finiteGreen ν B v E ε hε x y =
      Infra.resolventColumn (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) B
        ((E : ℂ) + (ε : ℂ) * Complex.I) y x := by
  rw [Infra.resolventColumn_of_mem _ _ _ x.2 y.2]
  unfold finiteGreen
  rw [hamiltonian_eq_restrictedOp]

                                                                                           
                


                                                                                           
                                                                               
                                      
                                                                          
                                                       
                                                      
                                     
                                        
                                        
                                      
                                      
                                     
                                                                                     
                                                                                            
              
                                                                                              
                                                                                          
                              
                                                             
                    
                                                                   
                                                      
                                              
                                     
                                                   
                                                  
                              
          
                                     
                                                                   
                                   
                
                                   
                                                                      
                                       
                                               
                                                            
                                                  
                         
                                                               
                                                                                 
                              
                                                                                  
                                  
                                                                                        
                                  
            
                                          
                                                 
                                                                
                  
                                      
                     
                     
                     
                                                    
                                                    
                                           
               


                                                                                           
                                                                         
                                                                                             
                       
                                      
                                      
                                    
                                                                                           
                                                                         
                                                               
                                                                               
                                   
                                                     
                                
                  


                                                                                               
                                           
                                                                                        
                                                                        
                                                          
                                                      
                                     
                                                  
                                  
                                                            
                            
                                                                    
                                          
                                          
                                                                                    
                                                                       
                                                 
                                                                                             
                                                        
           
                                       
                                                                                         
                           
                                                                             
                                                               
                                                   
                                                          
                        
            
                                                           
                                           
                                                              
               
                                                 
                                                                   
                                                                                                    
                       
                                                     
                                                                    
          
             
                                                                              
                                    
                                           
                                           
                                                                      
                                                                      
                                          
                                 
                                       
                                        

end FroehlichSpencer.T12

end
