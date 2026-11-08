/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MoveLedgerStage88

/-! # Selecting fresh physical catalyst triangles for a deployed configuration

For every active vertex `y` of a configuration `Y` whose degrees are all `0`
or `2`, an active incident edge `y w` of `Y` supplies an allowed type
`{p y, p w, k} ∈ F`. We select a fresh physical triangle
`(co y, cs y, ct y)` with `p (co y) = p y` and label multiset
`{p y, p (cs y), p (ct y)} ∈ F`, using only the compatible four-root supply
`CompatibleSupply p F G a` (queries with at most two roots), the forbidden
degree bound on `B`, and an explicit budget. All chosen triples are mutually
vertex-disjoint, avoid a forbidden vertex set `Z₀` (which the caller makes
contain every active vertex), and all their edges are real edges of `G`
outside `B ∪ L`. Their union `D` has an actual decomposition and `|D| ≤ 3|Y|`.
Nothing about the later insertion is assumed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystSelectionStage89

open Finset AntiEdgeSelection TypedTransformer PairMoveSelectionStage85

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The three edges of the catalyst triangle with centre `o`. -/
def catEdges (o s u : V) : Finset (Sym2 V) := {s(o, s), s(o, u), s(s, u)}

/-- The three vertices of a catalyst triangle. -/
def catVerts (o s u : V) : Finset V := {o, s, u}

theorem triEdges_eq_catEdges {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = catEdges x y z := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  simp only [triEdges, catEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
    mem_insert, mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

/-- One catalyst triangle with an allowed label multiset decomposes. -/
theorem catalyst_decomp {p : V → Fin t} {F : Finset (Multiset (Fin t))} {o s u : V}
    (h1 : o ≠ s) (h2 : o ≠ u) (h3 : s ≠ u) (hl : Link F (p o) (p s) (p u)) :
    HasDecomp p F (catEdges o s u) := by
  refine ⟨{{o, s, u}}, ?_, by simp, by simp [triEdges_eq_catEdges h1 h2 h3]⟩
  intro T hT
  rw [mem_singleton.mp hT]
  refine ⟨?_, ?_⟩
  · rw [card_insert_of_notMem (by simp [h1, h2]), card_pair h3]
  · rw [insert_val_of_notMem (by simp [h1, h2]), insert_val_of_notMem (by simp [h3])]
    simpa [Link] using hl

theorem mem_catVerts_of_mem {o s u v : V} {e : Sym2 V} (he : e ∈ catEdges o s u)
    (hv : v ∈ e) : v ∈ catVerts o s u := by
  simp only [catEdges, mem_insert, mem_singleton] at he
  simp only [catVerts, mem_insert, mem_singleton]
  rcases he with rfl | rfl | rfl <;> simp only [Sym2.mem_iff] at hv <;> tauto

                                                                      
                 
                                                                                            

                                                                      
                 
                                                                                            

                                                            
theorem catEdges_disjoint {o s u o' s' u' : V}
    (h : Disjoint (catVerts o s u) (catVerts o' s' u')) :
    Disjoint (catEdges o s u) (catEdges o' s' u') := by
  rw [disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
  exact disjoint_left.mp h (mem_catVerts_of_mem he (Sym2.mem_mk_left a b))
    (mem_catVerts_of_mem he' (Sym2.mem_mk_left a b))

variable [Fintype V]

/-- The properties of a selected catalyst family indexed by `A`. -/
structure Catalysts (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B L : Finset (Sym2 V)) (Z₀ A : Finset V) (co cs ct : V → V) :
    Prop where
  /-- The centre has the label of its active vertex. -/
  label : ∀ y ∈ A, p (co y) = p y
  /-- The label multiset `{p y, p (cs y), p (ct y)}` is an allowed type. -/
  link : ∀ y ∈ A, Link F (p y) (p (cs y)) (p (ct y))
  distinct : ∀ y ∈ A, co y ≠ cs y ∧ co y ≠ ct y ∧ cs y ≠ ct y
  real : ∀ y ∈ A, catEdges (co y) (cs y) (ct y) ⊆ G.edgeFinset
  /-- Every catalyst vertex avoids the forbidden vertex set. -/
  fresh : ∀ y ∈ A, Disjoint (catVerts (co y) (cs y) (ct y)) Z₀
  /-- Distinct active vertices get vertex-disjoint triangles. -/
  vdisj : ∀ y ∈ A, ∀ y' ∈ A, y ≠ y' →
    Disjoint (catVerts (co y) (cs y) (ct y)) (catVerts (co y') (cs y') (ct y'))
  /-- Every catalyst edge avoids `B` and the ledger `L`. -/
  avoid : ∀ y ∈ A, Disjoint (catEdges (co y) (cs y) (ct y)) (B ∪ L)

/-- The union of the selected catalyst triangles. -/
def catUnion (A : Finset V) (co cs ct : V → V) : Finset (Sym2 V) :=
  A.biUnion fun y => catEdges (co y) (cs y) (ct y)

                             
                                                               
                                                  

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B L : Finset (Sym2 V)} {Z₀ A : Finset V} {co cs ct : V → V}

theorem Catalysts.mono {A' : Finset V} (h : Catalysts p F G B L Z₀ A co cs ct) (hA : A' ⊆ A) :
    Catalysts p F G B L Z₀ A' co cs ct :=
  ⟨fun y hy => h.label y (hA hy), fun y hy => h.link y (hA hy),
    fun y hy => h.distinct y (hA hy), fun y hy => h.real y (hA hy),
    fun y hy => h.fresh y (hA hy), fun y hy y' hy' => h.vdisj y (hA hy) y' (hA hy'),
    fun y hy => h.avoid y (hA hy)⟩

                   
                                                            
                                                 
                 
                                 
                                                                      
                                                                  

                   
                                                               
                                                    
                    
                                 
                                                                      
                                                                  

                                                                      
                                            
            
                                         
                      

                                                                       
                                                
                    
            
                                         
                                          

                                                                     
                                              
                    
            
                                         
                                          

                                                              
theorem Catalysts.decomp (h : Catalysts p F G B L Z₀ A co cs ct) :
    HasDecomp p F (catUnion A co cs ct) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp [catUnion]⟩
  | @insert y A hy ih =>
    have hA := h.mono (subset_insert y A)
    have hy' : y ∈ insert y A := mem_insert_self y A
    obtain ⟨d1, d2, d3⟩ := h.distinct y hy'
    have hl : Link F (p (co y)) (p (cs y)) (p (ct y)) := by
      rw [h.label y hy']
      exact h.link y hy'
    have hdec := catalyst_decomp d1 d2 d3 hl
    have hdis : Disjoint (catEdges (co y) (cs y) (ct y)) (catUnion A co cs ct) := by
      rw [disjoint_left]
      intro e he he'
      obtain ⟨y', hy'A, he'⟩ := mem_biUnion.mp he'
      have hne : y ≠ y' := fun hh => hy (hh ▸ hy'A)
      exact disjoint_left.mp (catEdges_disjoint
        (h.vdisj y hy' y' (mem_insert_of_mem hy'A) hne)) he he'
    have heq : catUnion (insert y A) co cs ct =
        catEdges (co y) (cs y) (ct y) ∪ catUnion A co cs ct := by
      simp [catUnion, biUnion_insert]
    rw [heq]
    exact hdec.union (ih hA) hdis

end

                                                                            
                                                                         
                                                                        
                                                                            
                                                                     
                                                                  
                                                      
                                                                                 
                                  
                                                        
                                                          
                                                                 
         
                                            
            
             
                                                                                       
                        
                  
                                                            
                                                    
                                                                                  
                                      
                                           
                                            
                           
                                                                                            
                                                                  
                                                
                                                        
                                                           
                                                                      
              
                                                       
                                                                              
                                                                                         
              
                                                       
                 
                                                                                  
                                                                                 
                        
                                         
                
                                   
                                                    
                                                                                  
                                                
                                                                                           
                                    
                       
                                            
                
                                                 
                              
                
                                  
                
                                                                 
                                                                                     
                                                                                         
                                                                                  
                                           
                                                                                              
                                    
                                                                      
                                                                      
                                                                                          
                                                           
                                                                               
                                                  
                
                                                           
                                                   
                                                                                       
                                                             
                                                                                   
                  
                                                
                                      
                                                                                         
                                                                          
                  
                                                             
                                      
                                                                                             
                                                                   
                                                                   
                                            
                        
                    
                         
                                    
                               
                        
                                                 
                                       
                  
                                             
                       
                                                   
                  
                                             
                                  
                                                                       
                  
                                             
                                                  
                                                                                            
                  
                                             
                            
                                                                                        
                  
                                             
                                        
                          
                      
                                                     
                                                                                         
                                                                                              
                    
                          
                      
                                                                                  
                             
                                                   
                                           
                
                                                                
                                                                  
                               
                
                                                                
                                                                  
                                      
                                                                
                                                                
                                                                  
                                                                
                                        
                  
                                             
                            
                                                                                         

                                                                   
def active (Y : Finset (Sym2 V)) : Finset V := univ.filter fun v => incidentLoad Y v = 2

                                                                          
                                                          
                                                                       
                                                               
                                  
                                                        
                                                               
                 
                   
                       
             
                                         
                                             
       

                                                                      
                                               
                                                                                       
                                             
                                                                               
               
                                            
                                    

                                                                                         
                                                                                         
                                                             
                                                 
            
                                                        
                                                           
                                                     
                                      
                                 
            
                                           
                                 
                      
                           
                                 
                      

                                                                            
                                                                            
                                                                          
                                                                             
                                                                          
                                                                            
                                                                           
                                                                           
                                                                        
                                                      
                                                                             
                                                               
                                                             
                                                           
                                   
                                                               
                                                                    
                                                
                                                    
                                                   
                                                       
                                                            
                                                 
                                                                        
                                      
                                                                            
                                                
                                
              
                                                          
                                                             
                                                       
                                                          
                                                                                   
              
                                

end PartitionedTriangleAbsorption.CatalystSelectionStage89
