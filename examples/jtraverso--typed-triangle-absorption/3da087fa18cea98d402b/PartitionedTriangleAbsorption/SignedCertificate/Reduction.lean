/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Basic

/-! # Two-mode solutions, absorbers and simple certificates

For a physical source `P`, a *two-mode solution* is a pair `(A, Q)` of edge sets with
`P, A, Q` pairwise disjoint, `Q` F0-decomposable and both `A ∪ P` and `A ∪ Q`
F0-decomposable (the *same* `A`). An *absorber* is an edge set `A` disjoint from `P` with
`A` and `A ∪ P` both F0-decomposable.

* `twoMode_of_absorber`: an absorber plus any decomposable `Q` disjoint from it gives a
  two-mode solution;
* `absorber_of_twoMode`: a two-mode solution `(A, Q)` gives the absorber `A ∪ Q`;
* `signedCert_of_absorber`: an absorber inside `G` gives a *simple* signed certificate of
  `P` (coefficients `±1`, positive triangles edge-disjoint, negative triangles
  edge-disjoint).

Thus the common-`A` problem is exactly the existence of a bounded absorber; the
destination `Q` is a free decomposable add-on. The part-pair counts of `Q` are **not**
forced by the two modes (see `SignedCertificate.Controls.typeCounts_not_forced`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

                                     
                                                                
                                                          

                                                                                
                                                                 
                                                                 
                                                   

                       
                                                                 
                                                                          
                                                                  
                                          

                                                         
theorem hasDecomp_union {p : V → Fin 2} {E₁ E₂ : Finset (Sym2 V)}
    (h₁ : HasDecomp p F0 E₁) (h₂ : HasDecomp p F0 E₂) (hd : Disjoint E₁ E₂) :
    HasDecomp p F0 (E₁ ∪ E₂) := by
  obtain ⟨D₁, hT₁, hP₁, hU₁⟩ := h₁
  obtain ⟨D₂, hT₂, hP₂, hU₂⟩ := h₂
  refine ⟨D₁ ∪ D₂, ?_, ?_, ?_⟩
  · intro s hs
    rcases mem_union.mp hs with h | h
    · exact hT₁ s h
    · exact hT₂ s h
  · have hsub₁ : ∀ s ∈ D₁, triEdges s ⊆ E₁ := fun s hs => hU₁ ▸ subset_biUnion_of_mem _ hs
    have hsub₂ : ∀ s ∈ D₂, triEdges s ⊆ E₂ := fun s hs => hU₂ ▸ subset_biUnion_of_mem _ hs
    intro s hs u hu hsu
    simp only [coe_union, Set.mem_union, mem_coe] at hs hu
    rcases hs with hs | hs <;> rcases hu with hu | hu
    · exact hP₁ hs hu hsu
    · exact hd.mono (hsub₁ s hs) (hsub₂ u hu)
    · exact (hd.mono (hsub₁ u hu) (hsub₂ s hs)).symm
    · exact hP₂ hs hu hsu
  · rw [union_biUnion, hU₁, hU₂]

                                                                                        
                                                                     
                                                                                
                           
                                        
                                                                                          

                                                
                                                                     
                                                          
                                            
                                                                 
                                      
                                       
           
                                                                   

                                                                              
                                                                         
                                                
                                                                           

                                                                                          
             
                                                                                         
                                                                                      
                         
                                                                                                 
                   
                                                                                        
              
             
                     
                            
                                
                             
                                                         
           
                                           
                 
                        
                     
                                                     
                                   
                   
                             
                                                       
           
                                                                     
                  
                                                  
                   

                       
                                                                                    
                                                                                              
                         
                 
                     
                                   
                                                                                
                         
                   
                  

                                                                                       
                                                                                      
                                                                                   
                                                                              
                                                                        
                                 
                                  
                                                                                                 
                                               
                                                         
                                         
                                     
                                                                                     
                                                         
                          
                                                                           
                                                                 
                              
                                  
                                                            
           
                             
                                                                                        
                                                             
                                                           
                                                           
                              
                                                   
                                                                             
                                                

end PartitionedTriangleAbsorption.SignedCertificate
