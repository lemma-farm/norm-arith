/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Defs

/-! # BlowupB.IntVec — aggregate divisibility and physical certificates for integer edge vectors

The reduction of the "Theorem B" route manipulates `ℤ`-valued edge functions (indicators of edge
sets with multiplicities and signs). This module provides:

* `edgeVecZ`, `degVecZ` — the aggregate vectors of an integer edge function, agreeing with
  `edgeVec`, `degVec` on indicators, and linear;
* `AggDivZ` — Definition 13.5 for integer edge functions; a lattice (closed under `+`, `-`, `•`),
  agreeing with `IsIntDiv` on indicators, containing every copy;
* `PhysCertZ`, `PhysCostZ` — physical certificates of integer edge functions with cost bounds,
  closed under sums with additive cost, and implying `AggDivZ`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### Aggregate vectors of integer edge functions -/

/-- The edge-count vector of an integer edge function. -/
def edgeVecZ (p : V → Fin t) (w : Sym2 V → ℤ) : Fin t → Fin t → ℤ :=
  ∑ e, w e • pairVec p e

/-- The degree vector of an integer edge function at `v`. -/
def degVecZ (p : V → Fin t) (w : Sym2 V → ℤ) (v : V) : Fin t → ℤ :=
  ∑ e, w e • degContrib p v e

                                                             
                                        
                                

                                                                    
                                          
                                 

omit [DecidableEq V] in
theorem edgeVecZ_add (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) :
    edgeVecZ p (w₁ + w₂) = edgeVecZ p w₁ + edgeVecZ p w₂ := by
  simp only [edgeVecZ, Pi.add_apply, add_smul, sum_add_distrib]

omit [DecidableEq V] in
theorem edgeVecZ_smul (p : V → Fin t) (a : ℤ) (w : Sym2 V → ℤ) :
    edgeVecZ p (a • w) = a • edgeVecZ p w := by
  simp only [edgeVecZ, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum]

                       
                                                       
                                         
                                                               

                       
                                                           
                                                              
                                                                 

omit [DecidableEq V] in
theorem edgeVecZ_zero (p : V → Fin t) : edgeVecZ p (0 : Sym2 V → ℤ) = 0 := by
  simp [edgeVecZ]

theorem degVecZ_add (p : V → Fin t) (w₁ w₂ : Sym2 V → ℤ) (v : V) :
    degVecZ p (w₁ + w₂) v = degVecZ p w₁ v + degVecZ p w₂ v := by
  simp only [degVecZ, Pi.add_apply, add_smul, sum_add_distrib]

theorem degVecZ_smul (p : V → Fin t) (a : ℤ) (w : Sym2 V → ℤ) (v : V) :
    degVecZ p (a • w) v = a • degVecZ p w v := by
  simp only [degVecZ, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum]

                                                              
                                           
                                                              

                                                                  
                                                                 
                                                               

theorem degVecZ_zero (p : V → Fin t) (v : V) : degVecZ p (0 : Sym2 V → ℤ) v = 0 := by
  simp [degVecZ]

/-! ### Aggregate divisibility of integer edge functions -/

/-- **Aggregate `F`-divisibility** of an integer edge function (Definition 13.5): the edge-count
vector lies in the lattice of the type edge vectors and every degree vector lies in the lattice of
the corresponding type degree vectors. -/
def AggDivZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (w : Sym2 V → ℤ) : Prop :=
  (∃ c : Multiset (Fin t) → ℤ, edgeVecZ p w = ∑ τ ∈ F, c τ • typeEdgeVec τ) ∧
    ∀ v : V, ∃ c : Multiset (Fin t) → ℤ,
      degVecZ p w v = ∑ τ ∈ F with p v ∈ τ, c τ • typeDegVec τ (p v)

                                                                        
                                                                       
                         
                    
                        

theorem AggDivZ.zero (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    AggDivZ p F (0 : Sym2 V → ℤ) :=
  ⟨⟨0, by simp [edgeVecZ_zero]⟩, fun v => ⟨0, by simp [degVecZ_zero]⟩⟩

theorem AggDivZ.add {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w₁ w₂ : Sym2 V → ℤ}
    (h₁ : AggDivZ p F w₁) (h₂ : AggDivZ p F w₂) : AggDivZ p F (w₁ + w₂) := by
  obtain ⟨⟨c₁, hc₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨c₂, hc₂⟩, hl₂⟩ := h₂
  refine ⟨⟨c₁ + c₂, ?_⟩, fun v => ?_⟩
  · rw [edgeVecZ_add, hc₁, hc₂, ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_smul]
  · obtain ⟨d₁, hd₁⟩ := hl₁ v
    obtain ⟨d₂, hd₂⟩ := hl₂ v
    refine ⟨d₁ + d₂, ?_⟩
    rw [degVecZ_add, hd₁, hd₂, ← sum_add_distrib]
    exact sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_smul]

theorem AggDivZ.smul {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w : Sym2 V → ℤ}
    (h : AggDivZ p F w) (a : ℤ) : AggDivZ p F (a • w) := by
  obtain ⟨⟨c, hc⟩, hl⟩ := h
  refine ⟨⟨a • c, ?_⟩, fun v => ?_⟩
  · rw [edgeVecZ_smul, hc, smul_sum]
    exact sum_congr rfl fun τ _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  · obtain ⟨d, hd⟩ := hl v
    refine ⟨a • d, ?_⟩
    rw [degVecZ_smul, hd, smul_sum]
    exact sum_congr rfl fun τ _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem AggDivZ.neg {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w : Sym2 V → ℤ}
    (h : AggDivZ p F w) : AggDivZ p F (-w) := by
  have := h.smul (-1)
  rwa [neg_one_smul] at this

theorem AggDivZ.sub {p : V → Fin t} {F : Finset (Multiset (Fin t))} {w₁ w₂ : Sym2 V → ℤ}
    (h₁ : AggDivZ p F w₁) (h₂ : AggDivZ p F w₂) : AggDivZ p F (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

theorem AggDivZ.sum {p : V → Fin t} {F : Finset (Multiset (Fin t))} {ι : Type*}
    (s : Finset ι) (f : ι → Sym2 V → ℤ) (h : ∀ i ∈ s, AggDivZ p F (f i)) :
    AggDivZ p F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact AggDivZ.zero p F
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

                                                                
                                                                                       
                                                                                    
                       
                                                   
                                                         
                                                           

                                                          

                                                                                                 
                                                   
def PhysCertZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (w : Sym2 V → ℤ) {ι : Type*} [Fintype ι] (T : ι → Finset V) (c : ι → ℤ) : Prop :=
  (∀ j, IsCopy p F G (T j)) ∧ ∀ e, w e = ∑ j, c j * indZ (triEdges (T j)) e

/-- `w` has a physical certificate of cost at most `K`. -/
def PhysCostZ (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (w : Sym2 V → ℤ) (K : ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : ι → Finset V) (c : ι → ℤ),
    PhysCertZ p F G w T c ∧ ∑ j, |c j| ≤ K

                   
                                                                                              
                                                                                  
                                                                  

                   
                                                                                 
                                                       
                                                                 

                   
                                                             
                                                                                               
                                                                                   
                                                                                         

omit [Fintype V] in
theorem PhysCostZ.zero (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) :
    PhysCostZ p F G (0 : Sym2 V → ℤ) 0 :=
  ⟨Fin 0, inferInstance, fun j => absurd j.2 (Nat.not_lt_zero _), fun _ => 0,
    ⟨fun j => absurd j.2 (Nat.not_lt_zero _), fun e => by simp⟩, by simp⟩

omit [Fintype V] in
theorem PhysCostZ.mono {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K K' : ℤ} (h : PhysCostZ p F G w K) (hK : K ≤ K') :
    PhysCostZ p F G w K' := by
  obtain ⟨ι, hι, T, c, hc, hK₀⟩ := h
  exact ⟨ι, hι, T, c, hc, hK₀.trans hK⟩

omit [Fintype V] in
theorem PhysCostZ.congr {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w w' : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) (hw : w = w') :
    PhysCostZ p F G w' K := hw ▸ h

omit [Fintype V] in
theorem PhysCostZ.add {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w₁ w₂ : Sym2 V → ℤ} {K₁ K₂ : ℤ} (h₁ : PhysCostZ p F G w₁ K₁) (h₂ : PhysCostZ p F G w₂ K₂) :
    PhysCostZ p F G (w₁ + w₂) (K₁ + K₂) := by
  obtain ⟨ι₁, hι₁, T₁, c₁, ⟨hT₁, hw₁⟩, hK₁⟩ := h₁
  obtain ⟨ι₂, hι₂, T₂, c₂, ⟨hT₂, hw₂⟩, hK₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim T₁ T₂, Sum.elim c₁ c₂, ⟨?_, fun e => ?_⟩, ?_⟩
  · rintro (j | j)
    · exact hT₁ j
    · exact hT₂ j
  · rw [Pi.add_apply, hw₁ e, hw₂ e, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_le_add hK₁ hK₂

omit [Fintype V] in
theorem PhysCostZ.smul {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) (a : ℤ) :
    PhysCostZ p F G (a • w) (|a| * K) := by
  obtain ⟨ι, hι, T, c, ⟨hT, hw⟩, hK⟩ := h
  refine ⟨ι, hι, T, a • c, ⟨hT, fun e => ?_⟩, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, hw e, mul_sum]
    exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · calc ∑ j, |(a • c) j| = |a| * ∑ j, |c j| := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      _ ≤ |a| * K := mul_le_mul_of_nonneg_left hK (abs_nonneg a)

omit [Fintype V] in
theorem PhysCostZ.neg {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w : Sym2 V → ℤ} {K : ℤ} (h : PhysCostZ p F G w K) : PhysCostZ p F G (-w) K := by
  have := h.smul (-1)
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

omit [Fintype V] in
theorem PhysCostZ.sub {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {w₁ w₂ : Sym2 V → ℤ} {K₁ K₂ : ℤ} (h₁ : PhysCostZ p F G w₁ K₁) (h₂ : PhysCostZ p F G w₂ K₂) :
    PhysCostZ p F G (w₁ - w₂) (K₁ + K₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem PhysCostZ.sum {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ) (K : ι → ℤ)
    (h : ∀ i ∈ s, PhysCostZ p F G (f i) (K i)) :
    PhysCostZ p F G (∑ i ∈ s, f i) (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact PhysCostZ.zero p F G
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-! ### Physical ⇒ aggregate, for integer edge functions -/

                                                                                        
                                                                                                
                                                                           
                                                     
                          
                                                      
                                          
                                                                     
         
                                     
                                                                 

                                                                                                
                                                                            
                                 
                               

end PartitionedTriangleAbsorption.BlowupB
