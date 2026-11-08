/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPieceConditions
public import PartitionedTriangleAbsorption.TypedRefinerCharge
public import PartitionedTriangleAbsorption.UniversalRefiner.Basic

/-! # The F0 charge, embeddings and charge tokens

* `edge_charge`: an edge between equal parts has charge `-4`, a crossing edge `+2`
  (`charge = pair chi0 ∘ edgeVec`, i.e. twice `e₀₁ - 2e₀₀ - 2e₁₁`);
* `four_dvd_charge`: every loopless even edge set has charge divisible by `4`;
* `isIntDiv_of_charge`: a loopless even edge set of charge `0` is integrally
  F0-divisible (`TypedPieceConditions.F0_isIntDiv_iff`);
* transport of loads, looplessness and charge along injective vertex maps;
* the two charge tokens on `Fin 8`: a `4`-cycle of charge `-4` and an `8`-cycle of charge
  `+4`, both even at every vertex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.RefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks

/-! ### The F0 charge -/

section Charge

variable {W : Type*} [DecidableEq W]

omit [DecidableEq W] in
theorem edge_charge (pw : W → Fin 2) {a b : W} :
    pair chi0 (pairVec pw s(a, b)) = if pw a = pw b then -4 else 2 := by
  rw [pair_pairVec]
  generalize pw a = x
  generalize pw b = y
  fin_cases x <;> fin_cases y <;> simp [chi0]

                       
                                                                            
                                             
                                       
                                           
                                 
            
                                     
                 
                                               

                       
                                                                              
                                 
                                       
                                        
                                 
            
                                     
                                    
                                                                
                                                                                  

                       
                                                               
                                                                                    
                                
                                                  
            

                                                                           
                                                                                               
                                                                        
                          
                                                 
                        
               
                                                                               
                            
                                              
                                              
                                     
                             
                                                        
                                                                      
              
                  
                     
                                                                               
                                                                

                                           
noncomputable def touched (E : Finset (Sym2 W)) : Finset W :=
  E.image UniversalRefiner.endA ∪ E.image UniversalRefiner.endB

theorem mem_touched {E : Finset (Sym2 W)} {e : Sym2 W} (he : e ∈ E) {v : W} (hv : v ∈ e) :
    v ∈ touched E := by
  rcases UniversalRefiner.mem_iff_endA_endB.mp hv with rfl | rfl
  · exact mem_union_left _ (mem_image_of_mem _ he)
  · exact mem_union_right _ (mem_image_of_mem _ he)

/-- **Even loopless edge sets have charge divisible by `4`.** -/
theorem four_dvd_charge (pw : W → Fin 2) {E : Finset (Sym2 W)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (4 : ℤ) ∣ charge chi0 pw E := by
  set S0 := (touched E).filter fun v => pw v = 0
  let n0 : Sym2 W → ℕ := fun e => (S0.filter fun v => v ∈ e).card
  have hswap : ∑ e ∈ E, n0 e = ∑ v ∈ S0, incidentLoad E v := by
    simp only [n0, incidentLoad, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hedge : ∀ e ∈ E, (4 : ℤ) ∣ pair chi0 (pairVec pw e) - 2 * (n0 e : ℤ) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := fun h => hloop _ he (by simp [h])
      have hfa : a ∈ touched E := mem_touched he (Sym2.mem_mk_left a b)
      have hfb : b ∈ touched E := mem_touched he (Sym2.mem_mk_right a b)
      have hn : S0.filter (fun v => v ∈ s(a, b)) =
          ({a, b} : Finset W).filter (fun v => pw v = 0) := by
        ext v
        simp only [S0, mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨-, h0⟩, h⟩; exact ⟨h, h0⟩
        · rintro ⟨h, h0⟩
          rcases h with rfl | rfl
          · exact ⟨⟨hfa, h0⟩, Or.inl rfl⟩
          · exact ⟨⟨hfb, h0⟩, Or.inr rfl⟩
      simp only [n0]
      rw [hn, edge_charge, filter_insert, filter_singleton]
      generalize pw a = x at *
      generalize pw b = y at *
      fin_cases x <;> fin_cases y <;> simp [hab]
  have h1 : (4 : ℤ) ∣ charge chi0 pw E - 2 * ∑ e ∈ E, (n0 e : ℤ) := by
    rw [charge_eq_sum, mul_sum, ← sum_sub_distrib]
    exact dvd_sum hedge
  have h2 : (4 : ℤ) ∣ 2 * ∑ e ∈ E, (n0 e : ℤ) := by
    have : ∑ e ∈ E, (n0 e : ℤ) = ((∑ v ∈ S0, incidentLoad E v : ℕ) : ℤ) := by
      rw [← hswap]; push_cast; rfl
    rw [this]
    have hev : Even (∑ v ∈ S0, incidentLoad E v) := even_sum _ fun v _ => heven v
    obtain ⟨r, hr⟩ := hev
    rw [hr]; push_cast
    exact ⟨r, by ring⟩
  have := dvd_add h1 h2
  simpa using this

end Charge

/-! ### Injective vertex maps -/

section Embedding

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Transport of an edge set along a vertex map. -/
def mapE (ι : α → β) (E : Finset (Sym2 α)) : Finset (Sym2 β) := E.image (Sym2.map ι)

                       
                                                                 
                                                    
             

                                                        
                                                           

                                                                                       
                                                                
                                                      

omit [DecidableEq α] in
theorem card_mapE {ι : α → β} (hι : Function.Injective ι) (E : Finset (Sym2 α)) :
    (mapE ι E).card = E.card := card_image_of_injective _ (Sym2.map.injective hι)

                       
                                                                                     
                                                             
             
                                                      

                       
                                                                                   
                                                                
            
                                         
                         
                

                                                                                             
                                                                    
                          
                   
                                                                               
                                     
                     
               
                                         
                                
                                                              

                       
                                                                              
                                                             
                     
                                        
                
                                       
                                           
                

omit [DecidableEq α] [DecidableEq β] in
theorem pairVec_map (pw : β → Fin 2) (ι : α → β) (e : Sym2 α) :
    pairVec pw (Sym2.map ι e) = pairVec (pw ∘ ι) e := by
  induction e using Sym2.ind with
  | _ a b => simp [pairVec]

                       
                                                                            
                                                                                    
                                                                                               
                         

end Embedding

/-! ### Charge tokens -/

/-- The minus token: a `4`-cycle on parts `0,0,1,1`. -/
def minusG : Finset (Sym2 (Fin 8)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

/-- The plus token: an `8`-cycle on parts `0,1,0,1,1,0,0,1`. -/
def plusG : Finset (Sym2 (Fin 8)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 0)}

                                                          

                                                         

                                                 
def gadget (b : Bool) : Finset (Sym2 (Fin 8)) := if b then plusG else minusG

                                                                              

                                                                     
                    

                                                                            
                                            

theorem gadget_card_le (b : Bool) : (gadget b).card ≤ 8 := by
  cases b <;> decide

                                  
                                                                     
         
                                                                         
                      
                                                                                              
                           
          
                                                   
                      
                                                                               
                                                                             
                                            
                           
          

                                                                                           
          
                                            

end PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
