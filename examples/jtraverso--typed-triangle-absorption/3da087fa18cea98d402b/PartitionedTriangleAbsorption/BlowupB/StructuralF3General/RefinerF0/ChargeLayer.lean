/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.RefinerF0.ChargeLayerSelect

/-! # The charge layer: from an even refiner to a typed F0 refiner

`EvenRefiner.charge_layer`: every even refiner of a loopless reserve `X0` on `W0` (with an
arbitrary part function `pw0`) yields, on `W0 ⊕ (Tok κ × Fin 8)`, a fixed remainder `R` and a
fixed library of integrally F0-divisible pieces that refines **every** integrally
F0-divisible leftover `L ⊆ X0` (`RefinerAssembly.RefinesReserve`).

Quantifier order: the robust graph `H`, the remainder and the library are fixed first; only
then is the leftover chosen. The old-vertex incidence of the whole library equals that of
the even refiner, every token vertex lies in boundedly many pieces, pieces grow by a factor
at most `9`, and the library size grows linearly.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

theorem card_Zd (T : Finset κ) :
    (E.Zd pw0 T).card = ∑ i ∈ E.lib \ T, E.mc pw0 i + ∑ i ∈ T, E.pc pw0 i := by
  unfold Zd
  rw [card_union_of_disjoint]
  · rw [card_biUnion, card_biUnion]
    · congr 1
      · exact sum_congr rfl fun i _ => by
          rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      · exact sum_congr rfl fun i _ => by
          rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
    · intro i _ i' _ hii'
      rw [Function.onFun, disjoint_left]
      intro d h1 h2
      obtain ⟨k, -, rfl⟩ := mem_image.mp h1
      obtain ⟨k', -, h⟩ := mem_image.mp h2
      simp only [Prod.mk.injEq] at h
      exact hii' h.1.symm
    · intro i _ i' _ hii'
      rw [Function.onFun, disjoint_left]
      intro d h1 h2
      obtain ⟨k, -, rfl⟩ := mem_image.mp h1
      obtain ⟨k', -, h⟩ := mem_image.mp h2
      simp only [Prod.mk.injEq] at h
      exact hii' h.1.symm
  · rw [disjoint_left]
    intro d h1 h2
    simp only [mem_biUnion, mem_image] at h1 h2
    obtain ⟨i, -, k, -, rfl⟩ := h1
    obtain ⟨i', -, k', -, h⟩ := h2
    simp at h

theorem card_Zs {T : Finset κ} (hT : T ⊆ E.lib) : (E.Zs pw0 T).card = (E.Zd pw0 T).card :=
  card_image_of_injOn fun _ hd _ hd' h =>
    E.slot_inj pw0 (E.Zd_subset pw0 hT hd) (E.Zd_subset pw0 hT hd') h

/-- **Charge conservation fixes the number of present variable slots.** -/
theorem card_Zs_eq {T : Finset κ} (hT : T ⊆ E.lib) (hdisT : (T : Set κ).PairwiseDisjoint E.P)
    {L0 : Finset (Sym2 W0)} (hL0 : L0 ⊆ X0) (hq : charge chi0 pw0 L0 = 0)
    (hU : T.biUnion E.P = E.R0 ∪ L0) : (E.Zs pw0 T).card = E.sNum pw0 := by
  have hR : charge chi0 pw0 E.R0 = 4 * ∑ i ∈ T, E.chg pw0 i := by
    have h1 : charge chi0 pw0 (T.biUnion E.P) = ∑ i ∈ T, charge chi0 pw0 (E.P i) :=
      charge_biUnion _ _ _ _ hdisT
    have hdis : Disjoint E.R0 L0 := disjoint_of_subset_right hL0 E.disjRX
    rw [hU, charge_union _ _ hdis, hq, add_zero] at h1
    rw [h1, mul_sum]
    exact sum_congr rfl fun i hi => E.charge_eq_four_chg pw0 (hT hi)
  have hc0 : charge chi0 pw0 E.R0 / 4 = ∑ i ∈ T, E.chg pw0 i := by
    rw [hR]; exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [card_Zs pw0 E hT, card_Zd pw0 E T, sNum, hc0]
  have hsplit : ∑ i ∈ E.lib, (E.mc pw0 i : ℤ) =
      ∑ i ∈ E.lib \ T, (E.mc pw0 i : ℤ) + ∑ i ∈ T, (E.mc pw0 i : ℤ) :=
    (sum_sdiff hT).symm
  have hchg : ∑ i ∈ T, E.chg pw0 i = ∑ i ∈ T, ((E.mc pw0 i : ℤ) - E.pc pw0 i) :=
    sum_congr rfl fun i _ => E.chg_eq pw0 i
  rw [hsplit, hchg, sum_sub_distrib]
  have : ∑ i ∈ E.lib \ T, (E.mc pw0 i : ℤ) + ∑ i ∈ T, (E.mc pw0 i : ℤ) -
      (∑ i ∈ T, (E.mc pw0 i : ℤ) - ∑ i ∈ T, (E.pc pw0 i : ℤ)) =
      ((∑ i ∈ E.lib \ T, E.mc pw0 i + ∑ i ∈ T, E.pc pw0 i : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

/-! ### Membership in the library -/

theorem ids_subset_allIds {m : ℕ} {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hHfst : ∀ h ∈ H, h.1 < m + E.sNum pw0)
    (hHsnd : ∀ h ∈ H, h.2 ∈ (range m).disjSum (range (E.z pw0)))
    {j : JIdx κ} (hj : j ∈ E.indices pw0 H) : E.ids pw0 j ⊆ E.allIds pw0 m := by
  intro t ht
  simp only [indices, mem_union, mem_image, Function.comp_apply] at hj
  simp only [allIds, mem_union, mem_image, mem_range]
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨h, hh, rfl⟩
  · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
    rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_false pw0 hi hk), rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨(i, k), (E.mem_relIdx pw0).mpr ⟨hi, hk⟩, rfl⟩))
  · obtain ⟨hi, hk⟩ := (E.mem_relIdx pw0).mp hr
    simp only [ids, idsRel, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_true pw0 hi hk), rfl⟩))
  · simp only [ids, idsMt, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inr ⟨h.1, hHfst h hh, rfl⟩)
    · have := hHsnd h hh
      rcases hh2 : h.2 with y | j'
      · rw [hh2] at this
        have : y < m := by simpa using this
        exact Or.inr ⟨y, this, by simp [minusId]⟩
      · rw [hh2] at this
        have : j' < E.z pw0 := by simpa using this
        exact Or.inl (Or.inl (Or.inr ⟨j', this, by simp [minusId]⟩))

                                                                                           
                                 
                     
                                                      
                     
                        

                                                                                             
                         

                                                                                  
                                                 
                              
                                                                                               

                

                                                          
                                                                  
                                               
                                        
                
                  
                                                                                            
                                            
                                     
                                                               
                                                                             
                                             
                                                                                    
                      
                 
                                         
                                                               
                                                       
                                                                                         
     

theorem card_filter_idsPar_le (t : Tok κ) :
    (E.lib.filter fun i => t ∈ E.idsPar pw0 i).card ≤ 1 := by
  refine card_le_one.mpr fun i hi i' hi' => ?_
  obtain ⟨hi1, ht1⟩ := mem_filter.mp hi
  obtain ⟨hi2, ht2⟩ := mem_filter.mp hi'
  simp only [idsPar, mem_union, mem_image, mem_range] at ht1 ht2
  rcases ht1 with ⟨k, hk, h1⟩ | ⟨k, hk, h1⟩ <;> rcases ht2 with ⟨k', hk', h2⟩ | ⟨k', hk', h2⟩
  · rw [← h2] at h1
    simp only [Tok.vm.injEq] at h1
    have := E.slot_inj pw0 (E.mem_D_false pw0 hi1 hk) (E.mem_D_false pw0 hi2 hk') h1
    simp only [Prod.mk.injEq] at this
    exact this.1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1
    simp only [Tok.pp.injEq] at h1
    exact h1.1

theorem card_filter_idsRel_le (t : Tok κ) :
    ((E.relIdx pw0).filter fun r => t ∈ E.idsRel pw0 r).card ≤ 1 := by
  refine card_le_one.mpr fun r hr r' hr' => ?_
  obtain ⟨hr1, ht1⟩ := mem_filter.mp hr
  obtain ⟨hr2, ht2⟩ := mem_filter.mp hr'
  obtain ⟨hi, hk⟩ := (E.mem_relIdx pw0).mp hr1
  obtain ⟨hi', hk'⟩ := (E.mem_relIdx pw0).mp hr2
  simp only [idsRel, mem_insert, mem_singleton] at ht1 ht2
  rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2 <;> rw [h2] at h1
  · simp only [Tok.pp.injEq] at h1
    exact Prod.ext h1.1.symm h1.2.symm
  · simp at h1
  · simp at h1
  · simp only [Tok.vm.injEq] at h1
    have := E.slot_inj pw0 (E.mem_D_true pw0 hi' hk') (E.mem_D_true pw0 hi hk) h1
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1.symm this.2.1.symm

theorem card_filter_idsMt_le {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24)
    (hdy : ∀ y, (H.filter fun h => h.2 = y).card ≤ 18) (t : Tok κ) :
    (H.filter fun h => t ∈ (idsMt h : Finset (Tok κ))).card ≤ 42 := by
  have hsub : (H.filter fun h => t ∈ (idsMt h : Finset (Tok κ))) ⊆
      (H.filter fun h => Tok.bp h.1 = t) ∪ (H.filter fun h => minusId h.2 = t) := by
    intro h hh
    obtain ⟨hh1, ht⟩ := mem_filter.mp hh
    simp only [idsMt, mem_insert, mem_singleton] at ht
    rcases ht with h1 | h1
    · exact mem_union_left _ (mem_filter.mpr ⟨hh1, h1.symm⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hh1, h1.symm⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 : (H.filter fun h => Tok.bp h.1 = t).card ≤ 24 := by
    rcases t with _ | _ | x | _
    · simp
    · simp
    · refine le_trans (card_le_card fun h hh => ?_) (hdx x)
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      exact mem_filter.mpr ⟨hh, by simpa using he⟩
    · simp
  have h2 : (H.filter fun h => minusId h.2 = t).card ≤ 18 := by
    by_cases ht : ∃ y, minusId y = t
    · obtain ⟨y, rfl⟩ := ht
      refine le_trans (card_le_card fun h hh => ?_) (hdy y)
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      exact mem_filter.mpr ⟨hh, minusId_injective he⟩
    · push Not at ht
      rw [card_eq_zero.mpr]
      · omega
      · exact filter_eq_empty_iff.mpr fun h _ => ht h.2
  omega

                                               
                                                      
                                                                                
                                                                                
                                        
                                  
                                                                       
                                                                  
                            
               
                                        
                    
                    
                                           
                                                                                   
                  
                                   
                                                                               
                                                                          
                       
                                                               
                       
                                                               
                       
                                                                
       

theorem card_le_of_fst {H : Finset (ℕ × (ℕ ⊕ ℕ))} {n : ℕ} (hfst : ∀ h ∈ H, h.1 < n)
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24) : H.card ≤ 24 * n := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range n)
    (fun h hh => mem_range.mpr (hfst h hh))]
  calc ∑ x ∈ range n, (H.filter fun h => h.1 = x).card ≤ ∑ _x ∈ range n, 24 :=
        sum_le_sum fun x _ => hdx x
    _ = 24 * n := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-! ### The main theorem -/

                        
                                                                                   
                           
                                                                                             
                                                                                         
                                                                                    
                                                                
                                            
                                                                             
                                                                    
                                                                                  
                                                                           
                        
                                      
                                                                                                
                                            
                                                  
                                                                                              
                                                                                 
                                                  
                          
                                                          
                   
                                                      
                                                        
                                                                      
                                                      
             
                                                                                              
                        
                                                                    
                                            
                                                        
                                                          
                                                         
                                                       
                                                                                   
                                                       
                
                                                                      
                                                                    
                                                                 
                                             
                                                      
                                                                       
                                                               
                           
                                                                            
                                                            
               
                                                                                          
                                                         
              
                                                        
                  
                                                                             
                                                               
                     
                                                                                         
                                                    
                         
                                                          
                          
                      
                                                               
                         
                                                          
                          
                                             
                                                                                  
                                                                          
                                                               
                                      
                                     
                                  
                                         
                                                                          
                                                               
                                                                              
                                 
                                                                     
                                               
                                       
                                   
             
                                                                        
                                                 
             
                                                                        
                                                 
             
                                       
                         
                                                   
                                                                             
                  
                                                                               
                                                                              
             

end EvenRefiner

end PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
