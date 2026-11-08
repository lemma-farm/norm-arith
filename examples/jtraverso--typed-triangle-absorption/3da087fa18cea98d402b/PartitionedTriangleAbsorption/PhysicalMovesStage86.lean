/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairMoveAssemblyStage85

/-! # Physical support of backwards pair-move assembly

The allowed edge set E is fixed. Each move carries its actual support in E;
the theorem below constructs an absorber in E, not merely an abstract edge set.
Existence of the move trace remains a separate producer obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalMovesStage86

open Finset PairMoveAssemblyStage85

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- A fresh trace whose added edges all belong to a fixed physical host. -/
inductive PhysicalMoves (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (E B : Finset (Sym2 V)) :
    Finset (Sym2 V) → Finset (Sym2 V) → Finset (Sym2 V) → ℕ → Prop
  | stop (U X : Finset (Sym2 V)) : PhysicalMoves p F E B U X X 0
  | step {U X Y Q R H : Finset (Sym2 V)} {n : ℕ}
      (history : X ⊆ U) (removed : Q ⊆ X)
      (fresh : Disjoint (H ∪ R) (B ∪ U))
      (physical : H ∪ R ⊆ E)
      (move : IsTransformer (p := p) (F := F) H Q R)
      (sizeH : H.card ≤ 7) (sizeR : R.card ≤ 2)
      (tail : PhysicalMoves p F E B (U ∪ H ∪ R) ((X \ Q) ∪ R) Y n) :
      PhysicalMoves p F E B U X Y (n + 1)

theorem PhysicalMoves.fresh {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) : FreshMoves p F B U X Y n := by
  induction h with
  | stop U X => exact .stop U X
  | step hX hQ hf _ hm hH hR _ ih => exact .step hX hQ hf hm hH hR ih

/-- A physical trace transports along an injective, label-preserving vertex map.
Support, freshness, the exact states and the number of moves are preserved. -/
theorem PhysicalMoves.map {W : Type*} [DecidableEq W]
    (f : V ↪ W) {q : W → Fin t} (hp : ∀ v, q (f v) = p v)
    {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) :
    PhysicalMoves q F (E.map (PhysicalHingeSupply.edgeEmb f))
      (B.map (PhysicalHingeSupply.edgeEmb f)) (U.map (PhysicalHingeSupply.edgeEmb f))
      (X.map (PhysicalHingeSupply.edgeEmb f)) (Y.map (PhysicalHingeSupply.edgeEmb f)) n := by
  induction h with
  | stop U X => exact .stop _ _
  | @step U X Y Q R H n hX hQ hf hphys hm hH hR ht ih =>
    have hmove : IsTransformer (p := q) (F := F)
        (H.map (PhysicalHingeSupply.edgeEmb f))
        (Q.map (PhysicalHingeSupply.edgeEmb f))
        (R.map (PhysicalHingeSupply.edgeEmb f)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_union]
        exact (disjoint_map _).mpr hm.1
      · rw [← map_union]
        exact PhysicalHingeSupply.hasDecomp_map f hp hm.2.1
      · rw [← map_union]
        exact PhysicalHingeSupply.hasDecomp_map f hp hm.2.2
    refine .step (map_subset_map.mpr hX) (map_subset_map.mpr hQ)
      (by rw [← map_union, ← map_union]; exact (disjoint_map _).mpr hf)
      (by rw [← map_union]; exact map_subset_map.mpr hphys) hmove
      (by simpa using hH) (by simpa using hR) ?_
    simpa only [map_union, map_sdiff] using ih

                                                                          
                                                                           
                                                                
                                        
                                                       
                  
                                                                        
                                                         
                                               
                              
                                                               
                              
                                                               
                                                    
                
                           
                                        
                                                    
                
                           
                                        
                                               
                
                                   
           
                      
                                                                    
                                         
                                                                     
                                                 
           
                                  

                                                                     
                                                                                
                                                           
                          
                                                        
                            
                                                       
                                           
                                                                 
                                             
                                                                      
                                                                  
                         

                                                                  
                                                                             
                                                                     
                                       
                                              
                                                           
                               
          

                                                                      
                                             
                                                
                                                               
       

end PartitionedTriangleAbsorption.PhysicalMovesStage86
