/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Splitting
public import PartitionedTriangleAbsorption.BlowupB.IntVec

/-! # BlowupB.KeevashBridge — nearly-complete absorbers from a typed Keevash interface

Two interfaces, stated in the language of this library:

* `KeevashTypedSpec F`: modelled on Keevash, *The existence of designs II*
  (arXiv 1802.05900v1), Theorem 3.1 (our own specialisation, not checked against any other
  formalisation; see `KeevashPadded` for the form of `L3F0.KeevashF0Spec`), with labels `Fin t × Fin 3`, one molecule per type, and
  `IsIntDiv` as lattice (`isIntDiv_iff_physDiv_uniform`). Regularity is stated with weights on
  typed triangles (`TriRegular`), extendability with common neighbourhoods (`CNExt`). Splitting
  triangle weights uniformly over the labelled embeddings gives Keevash's Definition 2.37;
  sequential embedding gives his Definitions 2.9–2.10.
* `ReserveSpec F h`: a sparse decomposable reserve `C` avoiding `B ∪ X` whose typed-triangle
  counts through every allowed pair are `(1 ± ε) κ n`, with type weights solving the load
  equations. (Paper proof: binomial graph with densities in the interior of the type cone,
  Chernoff, and an almost perfect packing by Keevash's Lemma 3.6; see
  `cegis/b0_refiner/KEEVASH_RESERVA_PRUEBA_20261011.md`.)

**`nearlyAbsorbing_of_keevash`**: the two interfaces give `NearlyAbsorbing F`. The deterministic
part is proved here: regularity of `C ∪ L` for every `L ⊆ X` with `|X| ≤ K`
(`triRegular_union`), monotonicity of extendability, and divisibility of `C ∪ L`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {t : ℕ}

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                        
                                                                                     
                
                                                                   
                                             
 
                                                                                          
                                                            
                                                                                     
                        
                      
                                                         
                                                                   
                                                                                   
 
                                                                                              
                                                                                               
                                   
def CNExt (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : Finset (Sym2 V)) (ω : ℝ)
    (h : ℕ) : Prop :=
  ∀ (S A : Finset V) (i : Fin t), S.card ≤ h → A ⊆ S → (∀ a ∈ A, AllowedPair F (p a) i) →
    ω * Fintype.card V ≤
      ((univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ A, s(a, v) ∈ G).card : ℝ)

end Defs

                                                                                         
                                                               
                   
                                                                                    
                                                                                    
                            
                                                                              
                              
                                                         
                                                                                
 
                                                                                                  
                                                                  
                                                                      
                                                
                                                                                        
                                                      
                                                                                      
                                       
                                                                                    
                                                                     
                                                         
                                                                     
                                                                     
                                                                                      
                                                     
                                                                                 
                                                                  
                                                                                      
                                     
 
section Deterministic

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                               
                                                                                  
                                                        
                                                 
       
 
                                                                                      
                                                                          
             
                                                              
                                                               
 
                                                            
                                                           
                                                        
               
                               
                      
                                  
 
                                                                                
                             
                                                                                 
                                                            
                                                                                      
               
                                                                           
                                      
                              
                               
                              
                               
                                                                        
                                      
                                      
                                                            
                                              
                                                                     
        
 
theorem CNExt.mono {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G G' : Finset (Sym2 V)}
    {ω ω' : ℝ} {h : ℕ} (hGG : G ⊆ G') (hω : ω' ≤ ω) (hC : CNExt p F G ω h) :
    CNExt p F G' ω' h := by
  intro S A i hS hA hal
  refine le_trans (mul_le_mul_of_nonneg_right hω (Nat.cast_nonneg _))
    (le_trans (hC S A i hS hA hal) ?_)
  exact_mod_cast card_le_card fun v hv => by
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    exact ⟨hv.1, hv.2.1, fun a ha => hGG (hv.2.2 a ha)⟩

                                                                                         
                                             
                                                                         
                                           
                                                                           
                                                                
                                               
                                                                             
                                                                         
                                                                  
                                                                            
                            
                                                                                             
                                     
                                               
                                                                                       
                                                 
                 
                          
                                                                        
                   
                                             
                                                        
                  
                                       
                                                                                                    
                                                                
                
                                       
                                          
                                                                
                                        
                                                                
                            
                                                             
                                                                
                 
                                                                                         
                                                                                        
                                                                               
                                                                   
                                                                                                
                       
                                                                              
                                                                            
                                                                        
                 
                                                       
                                                         
                                                  
                                                         
                                                                            
                                                                   
                                                             
                                                                       
                                                                         
                                                                            
                       
                                                        
                                      
                                                 
                                                                             
                                      
                                                                                     
                                             
                                                                             
                               
                              
                  
                  
                                                
                                                                      
                        
                             
 
end Deterministic

                                                                                     
                                                                                             
                                                          
                          
                                          
                                                   
                                            
                                                                   
                                                                                  
                                                                                 
                                                               
                                                                                               
                                                                                                
                                                                    
                                                                
                                                                                                  
                                                                
                                                                           
                                                          
                                                               
                                                                      
                                                                                            
                                                                                
                  
                                                     
                                     
                                                                               
                     
                                                                                     
                                                                                   
                                                                                        
                                                
                                                                       
                                
                                                           
                                   
                                                                                  
                                                                   
                                                    
                                                                            
                                                                                      
                                                                                      
                 
           
                                                                                    
                                                    
                                                                             
                                       
                                                                                            
                    
                                                           
                                                                 
                                                             
                                                                
                                                                             
                   
                
             
                                                             
                                                        
 
end PartitionedTriangleAbsorption.BlowupB
