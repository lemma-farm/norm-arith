/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Count
public import Mathlib
/-!
# Sorted eigenvalues and the counting function

The increasingly sorted eigenvalues `eigenvaluesAsc hH` of a finite Hermitian matrix are related to
`eigenvalueCount` and `eigenvalueCountLT`: the `k`-th smallest eigenvalue is `≤ E` iff more than
`k` eigenvalues are `≤ E`. Consequently the sorted eigenvalues are determined by the counting
function, which gives the form of the comparison used for Weyl's inequality.
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)

theorem eigenvalueCount_eq_card_eigenvaluesAsc (E : ℝ) :
    eigenvalueCount hH E = #{k | eigenvaluesAsc hH k ≤ E} := by
  refine Finset.card_equiv (ascIndex ι) fun i => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [eigenvalues_eq_eigenvaluesAsc_ascIndex hH i]

                                                          
                                                                 
                                                   
                                            
                                                  

theorem lt_card_filter_iff_of_downward {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ j k : Fin n, j ≤ k → P k → P j) (k : Fin n) :
    P k ↔ (k : ℕ) < #{j | P j} := by
  constructor
  · intro h
    have : Finset.Iic k ⊆ ({j | P j} : Finset (Fin n)) := fun j hj => by
      simp only [mem_filter, mem_univ, true_and]
      exact hP j k (mem_Iic.mp hj) h
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hk
    have : ({j | P j} : Finset (Fin n)) ⊆ Finset.Iio k := fun j hj => by
      simp only [mem_filter, mem_univ, true_and] at hj
      refine mem_Iio.mpr (lt_of_not_ge fun hkj => hk (hP k j hkj hj))
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega

/-- The `k`-th smallest eigenvalue is `≤ E` iff more than `k` eigenvalues are `≤ E`. -/
theorem eigenvaluesAsc_le_iff (k : Fin (Fintype.card ι)) (E : ℝ) :
    eigenvaluesAsc hH k ≤ E ↔ (k : ℕ) < eigenvalueCount hH E := by
  rw [eigenvalueCount_eq_card_eigenvaluesAsc]
  exact lt_card_filter_iff_of_downward (fun j => eigenvaluesAsc hH j ≤ E)
    (fun _ _ hjk h => (eigenvaluesAsc_monotone hH hjk).trans h) k

                                                                  
                                                                    
                                               
                                                                         
                                                                    

                                                                  
                                                              
                                              

                                                                  
                                                            
                                              

                                                    
theorem lt_eigenvalueCount_eigenvaluesAsc (k : Fin (Fintype.card ι)) :
    (k : ℕ) < eigenvalueCount hH (eigenvaluesAsc hH k) :=
  (eigenvaluesAsc_le_iff hH k _).mp le_rfl

                                                                        
                                                     
                                          

                                                                                    
                                                                                           
                                                                  
                                                                      
                                                 
                                                                                         
                                                  
                                     
                                                              

                                                            
theorem eigenvaluesAsc_le_add_of_eigenvalueCount_le {H₁ H₂ : Matrix ι ι ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) (δ : ℝ)
    (h : ∀ E, eigenvalueCount hH₂ E ≤ eigenvalueCount hH₁ (E + δ)) (k : Fin (Fintype.card ι)) :
    eigenvaluesAsc hH₁ k ≤ eigenvaluesAsc hH₂ k + δ :=
  (eigenvaluesAsc_le_iff hH₁ k _).mpr
    ((lt_eigenvalueCount_eigenvaluesAsc hH₂ k).trans_le (h _))

                                                              
                                                                                             
       
             
                   
                                    
                                                                          
                   
                                                                            

                                                                       
                                                                    
                                                                        

end FroehlichSpencer.Infra
