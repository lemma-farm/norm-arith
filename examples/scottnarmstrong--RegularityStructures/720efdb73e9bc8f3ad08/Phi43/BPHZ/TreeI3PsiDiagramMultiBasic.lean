/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiOuter
public import Phi43.BPHZ.TreeI3PsiTwoLevel
public import Phi43.BPHZ.TreeI3PsiSigma
public import Phi43.BPHZ.TreeI3PsiSlab
public import Phi43.BPHZ.TreeI3PsiChainBound

/-!
# Building blocks for the diagrams of `I(Ψ³)Ψ` with general exponents

* `TwoLevelLe G X`: a double-integral majorant `G` whose inner integrals are dominated by an
  integrable function of integral at most `X`; it yields integrability and a bound for every
  integrand dominated by `G`.
* the outer leaf and the inner integral of the chain diagram with the exponents
  `3`, `1 + α`, `1 + κ` (outer) and `4 + γ`, `2 + β` (inner), generalising the case
  `α = γ = 0`, `β = κ = δ` of `singularIntLe_outer_leaf` and `singularIntLe_inner`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- A function `G` of two space-time variables is a **two-level majorant with bound `X`** if, for
almost every `w`, `G w` is integrable and its integral is at most `H w`, where `H` is integrable
with `∫ H ≤ X`. -/
def TwoLevelLe (G : SpaceTime → SpaceTime → ℝ) (X : ℝ) : Prop :=
  (∀ᵐ w : SpaceTime ∂volume, Integrable (G w)) ∧
    ∃ H : SpaceTime → ℝ, SingularIntLe H X ∧ ∀ᵐ w : SpaceTime ∂volume, ∫ v, G w v ≤ H w

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem TwoLevelLe.add {G G' : SpaceTime → SpaceTime → ℝ} {X X' : ℝ} (h : TwoLevelLe G X)
    (h' : TwoLevelLe G' X') : TwoLevelLe (fun w v => G w v + G' w v) (X + X') := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  obtain ⟨hG', H', hH', hGH'⟩ := h'
  refine ⟨?_, fun w => H w + H' w, hH.add hH', ?_⟩
  · filter_upwards [hG, hG'] with w a b using a.add b
  · filter_upwards [hG, hG', hGH, hGH'] with w a b c d
    rw [integral_add a b]
    exact add_le_add c d

theorem TwoLevelLe.const_mul {G : SpaceTime → SpaceTime → ℝ} {X : ℝ} (h : TwoLevelLe G X) {c : ℝ}
    (hc : 0 ≤ c) : TwoLevelLe (fun w v => c * G w v) (c * X) := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  refine ⟨?_, fun w => c * H w, hH.const_mul hc, ?_⟩
  · filter_upwards [hG] with w a using a.const_mul c
  · filter_upwards [hGH] with w a
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left a hc

theorem TwoLevelLe.mono_right {G : SpaceTime → SpaceTime → ℝ} {X Y : ℝ} (h : TwoLevelLe G X)
    (hXY : X ≤ Y) : TwoLevelLe G Y := by
  obtain ⟨hG, H, hH, hGH⟩ := h
  exact ⟨hG, H, hH.mono_right hXY, hGH⟩

                                                                       
                                                                             
                                                        
                  

                                                                                      
                                                                             
                                                                                               
                                                                                 
                                                                                      
                               
                                                                       
                              

                                                                                     
                                                                            
                                                                       
                                                                                             
                                                                                           

                                                                                     
                                                                            
                                                                       
                                                                              
                                                                             
                                                                               

                                                                                       
                                                                            
                                                                       
                                                                              
                                                                             
                                                                               

                                                      
                                                                             
                                                            
                                    
                                         
                                                                          
                                                                                   
                                                                                    
                                                                           
                                  
                                                                                                 
                                                                                                   
                                                                                    
                                                                                         
             
                                                                                    
                                                                                         
             
                                                                                    
                                                                                         
             
                                                                 
                                                          
                                                    
                                                          
                                                    
                                                          
                                                    
                                                          
                                                    
                                                        
                                         
                                              
                                                                                               
                                                                                            
                    
          
                                         
                                              
                                                                                               
                                                                                            
                    
          
                                         
                                                

                                                                      
                                                                                 
                   
                                                                                    
                                                                         
                                                                                    
                                                                  
                                                                                 
                                                    
                                                                                         
                                                                                   
                                               
                      
                      
                      
                                                                     
                                                                     
                         
      

end RegularityStructures

end
