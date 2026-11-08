/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

/-! # Positive control: the double hexagon *is* absorbable in its scaled hosts

The first hexagon is absorbed by the central triangle `xyz`. The second is absorbed by a
24-edge gadget on six bulk vertices `w₁ … w₆` (classes `0, 3, 2, 3, 1, 2`):

* ears `x a' w₁, a' y w₂, y b' w₃, b' z w₄, z c' w₅, c' x w₆` and the hexagon-plus-triangle
  `w₁w₂w₃, w₃w₄w₅, w₅w₆w₁` decompose `A ∪ P`;
* `xyz, a'w₁w₂, b'w₃w₄, c'w₅w₆, xw₁w₆, yw₂w₃, zw₄w₅, w₁w₃w₅` decompose `A`.

This gadget is **not** 2-degenerate over the roots (as it must not be, by
`DoubleHexagon.no_degenerate_twoMode`): `w₁w₃w₅` and the three vertices around it need
common neighbours of more than two prescribed vertices. The finite checks are done on the
host with `m = 2` and transported along the class-preserving embedding into every `m ≥ 2`.

With the fresh destination of `SignedCertificate.Packing`, all conclusions of the Stage 49
candidate hold for this input with `C = 5` once `m ≥ 32` (`candidate_conclusion`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

open Finset TypedApplicationLinks

/-! ### Typed transport along an embedding -/

section Transport

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

/-- Edge embedding induced by a vertex embedding. -/
def edgeEmb (f : W ↪ V) : Sym2 W ↪ Sym2 V := ⟨Sym2.map f, Sym2.map.injective f.injective⟩

/-- Vertex-set embedding induced by a vertex embedding. -/
def setEmb (f : W ↪ V) : Finset W ↪ Finset V := ⟨fun s => s.map f, map_injective f⟩

theorem isDecomp_map (f : W ↪ V) {pW : W → Fin 2} {pV : V → Fin 2}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp pW F0 E D) : IsDecomp pV F0 (E.map (edgeEmb f)) (D.map (setEmb f)) := by
  obtain ⟨hT, hP, hU⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := mem_map.mp hs
    refine ⟨by simpa [setEmb] using (hT s' hs').1, ?_⟩
    simp only [setEmb, Function.Embedding.coeFn_mk, map_val, Multiset.map_map]
    have : pV ∘ f = pW := funext hp
    rw [this]; exact (hT s' hs').2
  · intro s hs u hu hsu
    simp only [coe_map, Set.mem_image, mem_coe] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    have hne : s' ≠ u' := fun h => hsu (by rw [h])
    simp only [Function.onFun, setEmb, Function.Embedding.coeFn_mk, triEdges_map]
    exact (disjoint_map _).mpr (hP hs' hu' hne)
  · rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, setEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨s, ⟨s', hs', rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      exact ⟨e', ⟨s', hs', he'⟩, rfl⟩
    · rintro ⟨e', ⟨s', hs', he'⟩, rfl⟩
      refine ⟨s'.map f, ⟨s', hs', rfl⟩, ?_⟩
      rw [triEdges_map]
      exact mem_map_of_mem _ he'

theorem hasDecomp_map (f : W ↪ V) {pW : W → Fin 2} {pV : V → Fin 2}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} (h : HasDecomp pW F0 E) :
    HasDecomp pV F0 (E.map (edgeEmb f)) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨_, isDecomp_map f hp hD⟩

end Transport

/-! ### The gadget, encoded on `Fin 15`

Vertices `0 … 8` are the roots; `9 … 14` are `w₁ … w₆`, placed in bulk classes
`0, 3, 2, 3, 1, 2` with indices `0, 0, 0, 1, 0, 1`. -/

                                            
                                                                                          

                                                                
                                                                                

                                                                
                                                                          

                                                                          
def AW : Finset (Sym2 (Fin 15)) :=
  {s(0, 1), s(1, 2), s(0, 2),
    s(6, 9), s(6, 10), s(0, 9), s(1, 10), s(9, 10),
    s(7, 11), s(7, 12), s(1, 11), s(2, 12), s(11, 12),
    s(8, 13), s(8, 14), s(2, 13), s(0, 14), s(13, 14),
    s(9, 14), s(10, 11), s(12, 13), s(9, 11), s(11, 13), s(9, 13)}

/-- The source on the gadget vertices. -/
def PW : Finset (Sym2 (Fin 15)) :=
  {s(0, 3), s(3, 1), s(1, 4), s(4, 2), s(2, 5), s(5, 0),
    s(0, 6), s(6, 1), s(1, 7), s(7, 2), s(2, 8), s(8, 0)}

                                           
                                    
                                                                                         
                

                                                              
                                    
                                                                                  
                                                                   

                                    
           
                

                                                               
theorem triEdges_triple {V : Type*} [DecidableEq V] (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_insert,
      mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hu | hu | hu, hv | hv | hv⟩, huv⟩ <;> subst hu <;> subst hv <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]

                                                                                      
                                                                        
                                                     
                                      

                                                        
            
                                                 
                                                                  
                                                 

                                                        
            
                                                 
                                                                                          
                                                 

                                                   
                                                      
                       
                                                      
                                                                    
                                                                    
         
                          
                                                                                           
                                                                                           
             
                  

                                                          
                                                      
                       
                                                      
                                                                                            
                                                                                            
         
                          
                                                                                           
                                                                                           
                
                  

                                             
              
                

                                                                                               
                                                         
                 
                

                                                                                  
                                   
                     
                

                                                                                             
                                       
                          
                

                                                                                                
                       
                

                                                                                            
                                  
                

                                                      
                
                

                                                                                  
              
                

                                                

                                              
                                                    
                                       
                                                                      

                            
                                                
                
               
                    
                                                                                         
                                                                                               
                     
                                                              

                                                                                          
                                       
             
                         
                                                     
                                                              

                                                                         
                                                  
                                           
             
                                                     
                                                                              
                                                   
                                                   
                                                                                                

                                                                                  
                          
         
       
                                 
            
                                                                                    
                               
                                                                               
                            
                 
                                      
                                                                               
                            
                 
                                      
               

                                                      
                                                                                        

                                                                            
                                         

                                                                                        
            
                                        
                                  
            
                                   
                                                         
                                
                               

                                                                           
                                                  
                                                     
                           
                     
                                  
                                             
                                                        
                                               
                                                        

                                                  

                                                                                       
                                       
                                                                      
              
                                                             
                             
                                                     
                                                             
                                           
                                 
                                 
            
                                                   
                                                                                
                                       
                                                 

                                                                                        
                                                                             
                                                           
                                                    
                                                                                     
                                                                        
                                                                 
                                                                 
                                                                 
                                                   
                                                       
                              
                         
                                                    
                                          
                                                    
                                                   
                   
                                 
                                            
                                        
                                            
                                       
                                  
              
                                       
                                                                               
                           
               
                                    
                                                        
                                                      
                                                                                  
         
                                  
                                                   
                            
                                            
                      
                   
                                   
                                                                                             
                                           
                                                                    
                                                                            
                                
                            
                                                            
                
                                                                              
                          
                                    
                          
                                                        
                                
                                                            
                                
                               
                                                         
                                                                             
            

end PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon
