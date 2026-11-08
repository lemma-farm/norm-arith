/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Combination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-! # A five-hub frame and reduction to hub patterns

A *frame* consists of five pairwise adjacent hubs `A0, A1, A2` (part `0`) and `C0, C1`
(part `1`) (`Hubs.Good`). A vertex `x` is *frame-attached* (`InW`) if it is adjacent to
`A0, C0, C1` (when `x ∈ V₀`) or to `A0, A1, C0` (when `x ∈ V₁`); its *anchor spoke* is
`x C0` resp. `x A0`.

`HubReduces f w M` says that `f` minus some hub pattern
`α·[A0C0] + β·π₀ + γ·π₁` (with `|α| + |β| + |γ| ≤ M`) is a physical triangle combination
of weight `≤ w`. The three gadgets are:

* `hubReduces_double_spoke`: twice an anchor spoke reduces with cost `(3, 1)`;
* `hubReduces_edge`: an edge between two attached vertices plus both anchor spokes reduces
  with cost `(3, 2)`;
* `realizes_of_hubReduces`: a charge-zero function that hub-reduces with cost `(w, M)` is
  realizable with weight `w + 7M` (the third hub `A2` supplies the rectangle).

Every identity is an identity of functions on all of `Sym2 V`, hence checks every edge.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

/-- Five hub vertices. -/
structure Hubs (V : Type*) where
  A0 : V
  A1 : V
  A2 : V
  C0 : V
  C1 : V

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

/-- The five hubs have the prescribed parts and are pairwise adjacent. -/
structure Hubs.Good (p : V → Fin 2) (G : SimpleGraph V) (H : Hubs V) : Prop where
  pA0 : p H.A0 = 0
  pA1 : p H.A1 = 0
  pA2 : p H.A2 = 0
  pC0 : p H.C0 = 1
  pC1 : p H.C1 = 1
  a0a1 : G.Adj H.A0 H.A1
  a0a2 : G.Adj H.A0 H.A2
  a1a2 : G.Adj H.A1 H.A2
  a0c0 : G.Adj H.A0 H.C0
  a0c1 : G.Adj H.A0 H.C1
  a1c0 : G.Adj H.A1 H.C0
  a1c1 : G.Adj H.A1 H.C1
  a2c0 : G.Adj H.A2 H.C0
  a2c1 : G.Adj H.A2 H.C1
  c0c1 : G.Adj H.C0 H.C1

                                    
                                                                          
                                                          
                                                          

                             
def anchor (p : V → Fin 2) (H : Hubs V) (x : V) : V := if p x = 0 then H.C0 else H.A0

/-- The anchor spoke of `x`. -/
def spoke (p : V → Fin 2) (H : Hubs V) (x : V) : Sym2 V → ℤ := edgeInd x (anchor p H x)

/-- Hub pattern `π₀ = -[A0C0] - [C0C1] + [A0C1]`. -/
def pi0 (H : Hubs V) : Sym2 V → ℤ := -edgeInd H.A0 H.C0 - edgeInd H.C0 H.C1 + edgeInd H.A0 H.C1

/-- Hub pattern `π₁ = -[A0C0] - [A0A1] + [A1C0]`. -/
def pi1 (H : Hubs V) : Sym2 V → ℤ := -edgeInd H.A0 H.C0 - edgeInd H.A0 H.A1 + edgeInd H.A1 H.C0

/-- The hub pattern `α·[A0C0] + β·π₀ + γ·π₁`. -/
def hubForm (H : Hubs V) (α β γ : ℤ) : Sym2 V → ℤ :=
  α • edgeInd H.A0 H.C0 + β • pi0 H + γ • pi1 H

/-- `f` reduces to a hub pattern of size `≤ M` with triangle weight `≤ w`. -/
def HubReduces (p : V → Fin 2) (G : SimpleGraph V) (H : Hubs V) (f : Sym2 V → ℤ)
    (w M : ℤ) : Prop :=
  ∃ α β γ : ℤ, |α| + |β| + |γ| ≤ M ∧ Realizes p G (f - hubForm H α β γ) w

                                                    
                      

namespace HubReduces

variable {H : Hubs V}

theorem of_realizes {f : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) :
    HubReduces p G H f w 0 :=
  ⟨0, 0, 0, by simp, h.congr (by funext e; simp [hubForm])⟩

theorem congr {f g : Sym2 V → ℤ} {w M : ℤ} (h : HubReduces p G H f w M) (hfg : f = g) :
    HubReduces p G H g w M := hfg ▸ h

theorem mono {f : Sym2 V → ℤ} {w M w' M' : ℤ} (h : HubReduces p G H f w M) (hw : w ≤ w')
    (hM : M ≤ M') : HubReduces p G H f w' M' := by
  obtain ⟨α, β, γ, h1, h2⟩ := h
  exact ⟨α, β, γ, h1.trans hM, h2.mono hw⟩

theorem add {f g : Sym2 V → ℤ} {w M w' M' : ℤ} (hf : HubReduces p G H f w M)
    (hg : HubReduces p G H g w' M') : HubReduces p G H (f + g) (w + w') (M + M') := by
  obtain ⟨α, β, γ, h1, h2⟩ := hf
  obtain ⟨α', β', γ', k1, k2⟩ := hg
  refine ⟨α + α', β + β', γ + γ', ?_, (h2.add k2).congr ?_⟩
  · have := abs_add_le α α'; have := abs_add_le β β'; have := abs_add_le γ γ'
    linarith
  · funext e; simp only [hubForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem smul {f : Sym2 V → ℤ} {w M : ℤ} (k : ℤ) (h : HubReduces p G H f w M) :
    HubReduces p G H (k • f) (|k| * w) (|k| * M) := by
  obtain ⟨α, β, γ, h1, h2⟩ := h
  refine ⟨k * α, k * β, k * γ, ?_, (h2.smul k).congr ?_⟩
  · simp only [abs_mul]
    nlinarith [abs_nonneg k]
  · funext e; simp only [hubForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem neg {f : Sym2 V → ℤ} {w M : ℤ} (h : HubReduces p G H f w M) :
    HubReduces p G H (-f) w M := by
  simpa using h.smul (-1)

theorem sub {f g : Sym2 V → ℤ} {w M w' M' : ℤ} (hf : HubReduces p G H f w M)
    (hg : HubReduces p G H g w' M') : HubReduces p G H (f - g) (w + w') (M + M') := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {α : Type*} (S : Finset α) (f : α → Sym2 V → ℤ) (w M : α → ℤ)
    (h : ∀ i ∈ S, HubReduces p G H (f i) (w i) (M i)) :
    HubReduces p G H (∑ i ∈ S, f i) (∑ i ∈ S, w i) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (of_realizes (H := H) (Realizes.zero : Realizes p G 0 0))
  | insert a S ha ih =>
    rw [sum_insert ha, sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a S)).add (ih fun i hi => h i (mem_insert_of_mem hi))

end HubReduces

variable {H : Hubs V}

                                                                                          
                                                                              
                                                
                                      
                                     
                                                                                        
                                                                                        
                                                                                        
                                                            
            
                                                                                     
                                               
        
                                     
                                                                                        
                                                                                        
                                                                                        
                                                            
            
                                                                                  
                                                             
        
        

                                                                            
                                                                          
                                                                        
                                
                                    
                                                                        
                                                                                       
                                                                                       
                                                          
          
                                                                        
                                                                         
      
      

                                                                                                 
                                                                                         
                       
                                                                        
                                                                                   
                                  
                                  
                                                                                 
                                                                                  
                                            
                                                    
                                                                     
                               
                                  
                                  
                                                                                 
                                                                                  
                                            

                                                         
                                            
                                                        
                                                                    
                                      
                                                                    
                                      
                                                                    
                                      
                                                                    
                                      
                                                               
                                      
                                                               
                                      
                                                               
                                      
                                                                                    
               
          
                                                                          
      
      

                                                         
                                            
                                                        
                                                                    
                                      
                                                                    
                                      
                                                                    
                                      
                                                                    
                                      
                                                               
                                      
                                                               
                                      
                                                               
                                      
                                                                                    
               
          
                                                                          
      
      

                                                      
                                                        
                                                                        
                                                                                        
           
      
      

                                                                                             
                                                       
                                                                           
                                                                                         
                               
                              
                                              
                                             
                                         
                                         
                                                        
            
                                                                                              
                  
         
                     
                      
                                        

end PartitionedTriangleAbsorption.IntegerCertificate
