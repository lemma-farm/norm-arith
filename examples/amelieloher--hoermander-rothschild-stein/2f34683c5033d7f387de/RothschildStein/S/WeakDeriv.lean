-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Transposes
public import RothschildStein.Definitions.hasWeakWordDeriv
public import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
variable (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
variable (Ω : Opens (Fin n → ℝ))

/-- A locally integrable function times a test is integrable
(BB Def. 2.1, pp. 67–68). -/
theorem integrable_mul_test {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Integrable (fun x => f x * φ x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f (φ : (Fin n → ℝ) → ℝ)).trans (subset_tsupport φ))).mp
  exact (hf.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport).mul_continuousOn φ.continuous.continuousOn φ.hasCompactSupport

/-- The empty weak word is the original locally integrable function
(BB Def. 2.1, pp. 67–68). -/
theorem hasWeakWordDeriv_nil {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    hasWeakWordDeriv X Ω [] f f := by
  exact ⟨hf, hf, fun _ => rfl⟩

/-- Uniqueness of a weak word derivative up to null sets
(BB Def. 2.1, pp. 67–68; fundamental lemma). -/
theorem hasWeakWordDeriv_unique {I : List (Fin m)} {f g h : (Fin n → ℝ) → ℝ}
    (hg : hasWeakWordDeriv X Ω I f g) (hh : hasWeakWordDeriv X Ω I f h) :
    g =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] h := by
  have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.2.1.sub hh.2.1) (fun φ hφ hc hs => ?_)
  · rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [hz] with x hx
    intro hmem
    exact sub_eq_zero.mp (hx hmem)
  · let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, hs⟩
    have hi := (hg.2.2 ψ).trans (hh.2.2 ψ).symm
    have hig := (integrable_mul_test Ω hg.2.1 ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
    have hih := (integrable_mul_test Ω hh.2.1 ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
    change (∫ x in (Ω : Set (Fin n → ℝ)), g x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), h x * φ x at hi
    change IntegrableOn (fun x => g x * φ x) (Ω : Set (Fin n → ℝ)) volume at hig
    change IntegrableOn (fun x => h x * φ x) (Ω : Set (Fin n → ℝ)) volume at hih
    have he : (∫ x in (Ω : Set (Fin n → ℝ)), (g x - h x) * φ x) = 0 := by
      simp_rw [sub_mul]
      rw [integral_sub hig hih, hi, sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := (Ω : Set (Fin n → ℝ))) (fun x hx => by
        have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
        simp [hzero])]
    simpa only [smul_eq_mul, Pi.sub_apply, mul_comm] using he

/-- The one-shot cons word is precisely the derivative of its suffix
(BB p. 77; suffix). -/
theorem hasWeakWordDeriv_cons_iff
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g h : (Fin n → ℝ) → ℝ}
    (hh : hasWeakWordDeriv X Ω I f h) (i : Fin m) :
    hasWeakWordDeriv X Ω (i :: I) f g ↔ hasWeakWordDeriv X Ω [i] h g := by
  constructor
  · intro hg
    refine ⟨hh.2.1, hg.2.1, fun φ => ?_⟩
    rw [hg.2.2 φ, wordTranspose, wordTranspose, wordTranspose]
    have hi := hh.2.2 (fieldTransposeTest Ω (X i) (hX i) φ)
    simpa only [fieldTransposeTest_coe] using hi.symm
  · intro hg
    refine ⟨hh.1, hg.2.1, fun φ => ?_⟩
    rw [hg.2.2 φ, wordTranspose, wordTranspose, wordTranspose]
    have hi := hh.2.2 (fieldTransposeTest Ω (X i) (hX i) φ)
    simpa only [fieldTransposeTest_coe] using hi

                                                              
                            
                                                                 
                                                      
                                                                             
                                                                              
                                                        
                                                                                           
                                                                                           
                                                                                                                       
                                                                                                                       
                                                 
                   
                                                                                   

                                                                                
                                                                        
                                              
                                                                      
                                                
                                         
              

                                                                        
                                                         
                                                        
                                              
                                                                       
                                                          
                                      
                                                                    
                    
                                                              
                                            
                                                                                   
              
                                                                           
                                                                                 
             
                                                              
                                            
                                                                                
                                            
                                                    
                                                             
                                                    
                                                                   
                                                          
                                                              
                                                          
                                                        
          

                                                                  
                                                  
                                                          
                                       
                                                                       

                                                                           
                                             
                                                                 
                                                               
                                                       
                                                                  
                                                   
                  
                                                  
                  
                            
                                                  
                                                                                     

                                                                        
                        
                                                                                  
                                    
                                                         
                                                           
                                      
                                                    
      
                                                
                                                  
                                               
                                                                            
                                                                     
                                          

                                                                       
                                                            
                                                         
                                                        
                                              
                                    
                                                                     
                                                                  
                                                 
                                                          
                                                                    

end RothschildStein.S
