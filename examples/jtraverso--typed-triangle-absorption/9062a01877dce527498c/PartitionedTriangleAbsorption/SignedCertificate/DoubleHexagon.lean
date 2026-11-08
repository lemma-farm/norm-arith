/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Packing

/-! # The double hexagon: an actual signed-certificate input that defeats pairwise supply

Roots (`Fin 9`): `0 = x, 1 = y, 2 = z, 3 = a, 4 = b, 5 = c, 6 = a', 7 = b', 8 = c'`, with
parts `x,y,b,b' ∈ V₀` and `z,a,c,a',c' ∈ V₁`. The source is the union of two hexagons

  `P = (x a y b z c) ∪ (x a' y b' z c')`  (12 edges, every root of even degree).

The host on `Fin 9 ⊕ (Fin 4 × Fin m)` has root–root edges exactly `P ∪ {xy, yz, zx}`,
four bulk classes (two per part, complete multipartite between distinct classes) and all
root–bulk edges. It is F0-anti-edgeful with `α = 1/5` for `m ≥ 9`.

`P` has the actual signed physical certificate
`xay + ybz + zcx + xa'y + yb'z + zc'x - 2·xyz` of weight `8` (a negative coefficient is
essential). Every root has even degree, `|P| = 12`, `e₀₀ = e₁₁ = 2`, `e₀₁ = 8`.

`no_degenerate_twoMode`: no two-mode solution `(A, Q)` (with `A ⊆ E(G)`, `Q` outside the
roots) has `A ∪ P ∪ Q` 2-degenerate over the roots. Consequently the pairwise-supply version
of the Stage 49 candidate is false (`not_pairSupplyCandidate`). This is **not** a refutation
of the candidate itself: `DoubleHexagonAbsorber` exhibits a bounded absorber in the same
hosts.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

open Finset TypedApplicationLinks

/-! ### Abstract ear lemmas -/

section Ears

variable {V : Type*} [DecidableEq V]

                                                                                         
                                         
                                                                                  
                                                            
                                                                                  
                                   
                            
                                                  
                        
                                                                            
                                                          
               
                 
                                            
                          
                  
                         
                             
                              
                                             
                
         
                              
                 
                                                                               
                                
                        
                                

                                                                                      
                                                                             
                                                                                     
                                                 
                                             
                                                                                       
                            
                
                                                         
                                                                
                        
                    
                                                    
                                                         
                                          
                                                  
                      
              
         
                       
             
                                               
                                                             
                                                         
                             
                                     
         
                                                 
                                                   
                                                    

end Ears

/-! ### The roots -/

/-- The source on the roots: two hexagons through `x, y, z`. -/
def Pc : Finset (Sym2 (Fin 9)) :=
  {s(0, 3), s(3, 1), s(1, 4), s(4, 2), s(2, 5), s(5, 0),
    s(0, 6), s(6, 1), s(1, 7), s(7, 2), s(2, 8), s(8, 0)}

/-- The central triangle `xyz`. -/
def tc : Finset (Sym2 (Fin 9)) := {s(0, 1), s(1, 2), s(0, 2)}

/-- Root parts. -/
def rootPart : Fin 9 → Fin 2 := ![0, 0, 1, 1, 0, 1, 1, 0, 1]

/-- Parts of the four bulk classes. -/
def classPart : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The seven certificate triangles. -/
def triC : Fin 7 → Finset (Fin 9) :=
  ![{0, 3, 1}, {1, 4, 2}, {2, 5, 0}, {0, 6, 1}, {1, 7, 2}, {2, 8, 0}, {0, 1, 2}]

                                                                          
                                               

theorem root_irrefl : ∀ i : Fin 9, s(i, i) ∉ Pc ∪ tc := by decide

                                  
                                                                        
                                  
        

                                                                                    
                                                               
                               
        

                                                   
                        
        

                                                                   
                                                                                                 
                                     
              
        

                   

                                                                   
abbrev HV (m : ℕ) := Fin 9 ⊕ (Fin 4 × Fin m)

/-- Host parts. -/
def part (m : ℕ) : HV m → Fin 2
  | .inl i => rootPart i
  | .inr q => classPart q.1

/-- Host adjacency. -/
def hAdj (m : ℕ) : HV m → HV m → Prop
  | .inl i, .inl j => s(i, j) ∈ Pc ∪ tc
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr q, .inr q' => q.1 ≠ q'.1

instance (m : ℕ) : DecidableRel (hAdj m) := fun u v => by
  cases u <;> cases v <;> unfold hAdj <;> infer_instance

/-- The scaled host graph. -/
def host (m : ℕ) : SimpleGraph (HV m) where
  Adj := hAdj m
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp only [hAdj] at h ⊢
    · rwa [Sym2.eq_swap]
    · exact Ne.symm h⟩
  loopless := ⟨fun u h => by
    cases u with
    | inl i => exact root_irrefl i h
    | inr q => exact h rfl⟩

instance (m : ℕ) : DecidableRel (host m).Adj := inferInstanceAs (DecidableRel (hAdj m))

                                                               
                                            

                                                  
                                                                     
                                                                                   
                                           
                                                                  
                     
        

                                   
def cls {m : ℕ} : HV m → Option (Fin 4)
  | .inl _ => none
  | .inr q => some q.1

                                                                                        
           
              
                            
                                                                  

                                                                                    
                                      
              
                    
                                                  

                                                                        
                                                                   
                                            
                                     
            
                                                                  
                                                                                    
                                                                     
                                                                                     
              
                                         
                                              
                                                                  
                                 
                                                                           
                              
              
                                                
                                                 
           
                                                           
                                                 
          

                                                                      
         
             
                       
                       

                                                           

                                  
def rootEmb (m : ℕ) : Fin 9 ↪ HV m := ⟨Sum.inl, Sum.inl_injective⟩

                                   
                                                       
                                                          

                               
                                                                

                                          
def tri (m : ℕ) (k : Fin 7) : Finset (HV m) := (triC k).map (rootEmb m)

/-- The excluded set `Z`: the nine roots. -/
def roots (m : ℕ) : Finset (HV m) := univ.map (rootEmb m)

                                                                  

theorem triEdges_map {W V : Type*} [DecidableEq W] [DecidableEq V] (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).map ⟨Sym2.map f, Sym2.map.injective f.injective⟩ := by
  simp only [map_eq_image, triEdges, sym2_image, filter_image, Sym2.isDiag_map f.injective]
  rfl

                                                                             
                                                                    
            
                                                         
                                 

                                                                              
                                                                                                 
                                                                 
                                                                 

                                                                                    
                                     
                                            
                       
                                                             
                             
                             
                                                   
                                              
            

                                                              
                                                                                    
                           
         
                                                            
                          
                                    
              
                                           
                                               
                            
                                                
                  
                                       
        
                                           
                          
                                                                                
                                                                                                

                                                              
            
                                        
                                  
            
                                   
                                                     
                                
                              

                                                                   
                 
                                      
                                          
                                     

                                   

                                                                                          
                                                                                     
         
                                                                                 
                                                                        
                                        
                                                                       
                                                 
                                                       
                                                       
                                                                         
                                   
                   
                                
                                         
                                                 
                                                        
                                         
                                                            
                                       
             
                             
                                                                    
                                     
                                           
                                                                     
                         
                                                                                
                                   
                      
                                                                                             
                         
                         
                              
                                                
                                                  
                                                                              
              
                               
                                                                                           
               
                                       
                                                                                          
                                                                                             
                                                                                            

                                                 

                                                                         
                                                                                             
               
                     

                                                                                           
                                                                          
                                                       
                                                                            
                                                                                         
                                                  
                                                                             
                                                                  
                                                
                                                                                      
                                 
                                                                                     
                                             
                                                                                       

                                                                                       
                                                                                    
                                                                           
                                                 
                                                                   
                                                                                         
                                                  
                                                                             
                                                                  
                                                
                                                                                      
                                                                                 

                                                                                       
                                                                      
                                                                               
                                   
                
                  
                                                                                               
                                                               
                                                                      
                                                                                          
                                                    

end PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon
