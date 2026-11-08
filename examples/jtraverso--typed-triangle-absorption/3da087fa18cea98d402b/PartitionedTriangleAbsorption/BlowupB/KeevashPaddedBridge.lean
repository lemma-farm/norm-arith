/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPadded
public import PartitionedTriangleAbsorption.BlowupB.KeevashReserve

/-! # BlowupB.KeevashPaddedBridge — the padded interface implies `KeevashTypedSpec`

**`keevashTypedSpec_of_padded`**: `KeevashPaddedSpec F → KeevashTypedSpec F` for every family of
3-element types. Ingredients:

* `paddedRegularT_of_triRegular`: triangle weights `y_T ∈ [ω/n, 1/(ω n)]` are split uniformly over
  the `N_T` class-respecting embeddings of the padded pattern onto `T`; loads are preserved
  exactly, and `(γ n − q)^{q−3} ≤ N_T ≤ 27 n^{q−3}` (lower bound by `count_ext` with no required
  pairs, upper bound by a product count);
* `extendableT_of_cnExt` (in `KeevashPadded`);
* the choice of `m` with `2^{50 q³} ≥ 1/γ`, so that classes of size `≥ γ n` are `≥ n / h_K`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Patterns

theorem card_fin_filter_lt {N k : ℕ} (h : k ≤ N) :
    (univ.filter fun j : Fin N => j.val < k).card = k := by
  have e : (univ.filter fun j : Fin N => j.val < k).map Fin.valEmbedding = range k := by
    ext a
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
  have := congrArg card e
  rw [card_map, card_range] at this
  exact this

theorem count_le_of_card_three {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) (c : Fin t) :
    τ.count c ≤ 3 := hτ ▸ Multiset.count_le_card c τ

theorem patPosT_map_fst (m : ℕ) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) :
    (patPosT m τ).val.map Prod.fst = τ := by
  classical
  ext c
  rw [Multiset.count_map]
  have e : ((patPosT m τ).val.filter fun x => c = x.1) = ((patPosT m τ).filter fun x => c = x.1).val :=
    rfl
  rw [e, card_val]
  have hbij : ((patPosT m τ).filter fun x => c = x.1) =
      (univ.filter fun j : Fin (m + 3) => j.val < τ.count c).map
        ⟨fun j => (c, j), fun a b h => (Prod.mk.inj h).2⟩ := by
    ext x
    simp only [patPosT, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨x.2, hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, rfl⟩
  rw [hbij, card_map, card_fin_filter_lt (by have := count_le_of_card_three hτ c; omega)]

theorem card_patPosT (m : ℕ) {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) :
    (patPosT m τ).card = 3 := by
  have := congrArg Multiset.card (patPosT_map_fst m hτ)
  rw [Multiset.card_map, card_val, hτ] at this
  exact this

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem copyTriT_val {m : ℕ} {p : V → Fin t} {τ : Multiset (Fin t)} {φ : PosT t m → V}
    (hφ : IsEmbT m p φ) : (copyTriT m τ φ).val = (patPosT m τ).val.map φ :=
  image_val_of_injOn (fun a _ b _ h => hφ.1 h)

theorem copyTriT_card {m : ℕ} {p : V → Fin t} {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3)
    {φ : PosT t m → V} (hφ : IsEmbT m p φ) : (copyTriT m τ φ).card = 3 := by
  rw [← card_val, copyTriT_val hφ, Multiset.card_map, card_val, card_patPosT m hτ]

                                                                                               
                                                                                  
                                         
                                                      
                                  
 
                                                                                 
                                                                          
                                                                                          
                                                                                   
                                              
            
                                                                     
                                                                      
            
                                              
            
                           
                                                   
                                                                            
                                                                      
                                    
                                                                              
                                                                                         
              
                              
                                          
                          
                        
                                                             
                                                             
                                                
                                                
                                                     
                         
                         
                            
             
                                                    
                                                      
                                     
                                      
          
                          
                
                          
                                                             
               
                   
                                                   
                                     
                                                                   
                                                                          
                                     
                                                                    
                                        
               
                                                           
 
end Patterns

section Split

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                            
                                                                                                   
                                                                                               
 
                                                                                                 
                                                                                  
                                                                           
                                                    
            
                                                                    
                                                                                  
                                                                  
                                                   
                                                                                                  
                     
                   
                              
                                      
                                                                                         
                                    
                                                               
                                             
                                      
                                                                                    
                            
                                                            
                                                    
                                                                                   
                          
                         
                                     
                                                                               
                                      
                       
                         
                  
                                             
                                                                
                                 
                          
                    
                
                                          
 
                                                                                                 
                                        
                                                                            
            
                                                                                      
                                                                                        
                                 
               
                                           
                              
            
                    
                      
                                             
                       
                                                                                         
                               
                                               
                                               
                                                                                    
                  
                                                                                        
                                                                                
                                        
                                                    
                                                                 
            
                                   
             
                  
                            
                        
                      
 
                                                 
theorem PaddedRegularT.mono {m : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω ω' c : ℝ} (hω' : 0 < ω') (h : ω' ≤ ω)
    (hR : PaddedRegularT m p F J ω c) : PaddedRegularT m p F J ω' c := by
  obtain ⟨y, hb, hl⟩ := hR
  refine ⟨y, fun τ hτ φ hφ => ?_, hl⟩
  obtain ⟨b1, b2⟩ := hb τ hτ φ hφ
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (qT t m - 2) := by positivity
  constructor
  · exact le_trans (div_le_div_of_nonneg_right h hn) b1
  · refine b2.trans ?_
    rcases hn.lt_or_eq with hn' | hn'
    · exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right h hn)
    · rw [← hn']; simp

/-- Monotonicity of template extendability in `ω`. -/
theorem ExtendableT.mono {K : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω ω' : ℝ} (h : ω' ≤ ω) (hE : ExtendableT K p F J ω) :
    ExtendableT K p F J ω' := fun k hk κ S T φ hinj hlab =>
  le_trans (mul_le_mul_of_nonneg_right h (by positivity)) (hE k hk κ S T φ hinj hlab)

end Split

end PartitionedTriangleAbsorption.BlowupB
