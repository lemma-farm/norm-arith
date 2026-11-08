/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagonAbsorber
public import PartitionedTriangleAbsorption.SignedCertificate.Localization
public import PartitionedTriangleAbsorption.CoherentTransformer.Refutation
public import PartitionedTriangleAbsorption.CloneSupply.Basic

/-! # Stage 49 controls

1. **Bridge control** (`BridgeControl`). Four cliques `A₀, A₁` (part `0`), `B₀, B₁`
   (part `1`) of order `L + 2`, all cross-part edges, and only the two bridges
   `a₀b₀, a₁b₁` between `A₀` and `A₁`. The host is F0-anti-edgeful with `α = 1/8`. The
   source is the union of the two physical F0 triangles `a₀b₀c₀, a₁b₁c₁`, with a
   *positive* certificate (both coefficients `+1`) and an F0 decomposition. Once
   `β n > 2`, every good clone of `a₀` lies in `A₀`, every good clone of `b₀` lies in `A₁`,
   and no two such clones outside the excluded set are adjacent: the old same-word
   destination (clone every position and keep every source edge) is impossible, already
   for the source edge `a₀b₀`. Good clones exist (`clone_a0_exists`, `clone_b0_exists`),
   so the failure is not vacuous.
2. **Star control** (`StarControl`). The physical 4-cycle source of the coherent
   transformer refutation has coarse F0 charge `2(e₀₀ + e₁₁) - e₀₁ = 2`, hence admits
   **no** signed physical F0 certificate. It is not an instance of the Stage 49 candidate.
3. **Item-5 control** (`CountControl`). Two modes alone do not force equal part-pair
   counts: a `001` triangle `P`, a disjoint `011` triangle `Q` and `A = ∅` form a two-mode
   solution with different `00`-counts. Equal counts are an additional requirement, which
   the fresh destination of `SignedCertificate.Packing` meets by construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

                                                                 
                                                                                  
                                                                 
                    
               
                                 
            
                                                              
                                          

namespace BridgeControl

open CloneSupply

variable (L : ℕ)

/-- Vertices: block (`0 = A₀, 1 = A₁, 2 = B₀, 3 = B₁`) and index. -/
abbrev BV := Fin 4 × Fin (L + 2)

/-- The host: cliques on blocks, all cross-part edges, two bridges `(0,i)(1,i)`, `i < 2`. -/
def host : SimpleGraph (BV L) where
  Adj u v := ¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) ∧
    (u.1.val = v.1.val ∨ u.1.val / 2 ≠ v.1.val / 2 ∨
      (u.1.val = 0 ∧ v.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2) ∨
      (v.1.val = 0 ∧ u.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2))
  symm := ⟨fun u v h => ⟨fun h' => h.1 ⟨h'.1.symm, h'.2.symm⟩, by omega⟩⟩
  loopless := ⟨fun u h => h.1 ⟨rfl, rfl⟩⟩

instance : DecidableRel (host L).Adj := fun u v =>
  inferInstanceAs (Decidable (¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) ∧
    (u.1.val = v.1.val ∨ u.1.val / 2 ≠ v.1.val / 2 ∨
      (u.1.val = 0 ∧ v.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2) ∨
      (v.1.val = 0 ∧ u.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2))))

                                                                                            
                                                    
                                                                     
                                                                               

                                                                     
def part (v : BV L) : Fin 2 := ⟨v.1.val / 2, by omega⟩

                                                                                     
                          

                                                              

                                                                                      
                                  

                               
def a0 : BV L := (0, 0)
def a1 : BV L := (0, 1)
def b0 : BV L := (1, 0)
def b1 : BV L := (1, 1)
def c0 : BV L := (2, 0)
def c1 : BV L := (2, 1)

                                                                          
                                                                          
                                                                          
                                                                          
                                                                          
                                                                          

                                                                               
                           
                    

                                                               
                    

                                
def T0 : Finset (BV L) := {a0 L, b0 L, c0 L}
def T1 : Finset (BV L) := {a1 L, b1 L, c1 L}

                                                             
                                                                   

                                       

                                                                                            
        

                                                                
                                                                                          
                                                                             
                                                              
       

                               
                                                                                              
                       
                                                
         
                        

                                                                                         
                                                                                       
                                     
            
                                                                                             
                           
                                                  
                                                                                         
                        
                                     
                                                         
                                              
                                                                               
                             
                  
                                                                               
                                                                        
                                                 
                                                           
                                                         
                            
                                                                                                   
                  
                                                                                    
                            
                                                   
                                                                        
                                                 
                                                                                                   
                  
                                                                                    
                            
                                                   
                                                                        
                                                 
                              
                                          
                                                                                         
                                                      
              
           
                                            
                                                                 
                                                 
          

                                                   

                                                     
                                           
                                             
        

                                                     
                                           
                                             
        

                                                    
                                                  
                                                         
                                                   
                                                                        
                                                            
       
                   

                                                    
                                                  
                                                         
                                                   
                                                                        
                                                                  
       
                   

                                                     
                            

                                                                 
def tri : Fin 2 → Finset (BV L) := ![T0 L, T1 L]

                                                                    
                                                                                    
                                   
               
                                    
                                    
                                                                                      
                       
              

                                                                        
                   

                                                                               
                                                           
                                   
              
                                               
                            
                                              
                                              
                       
                                                                                             
                                                         
                          
                                                            
                                                                   
                          
                                               

                                                      
            
                                 
                                       
                                   
              
                                                                                
           
                                             
                                             

                                                 
                            
                                                                                       
                  
                                 
                        

                                                
                             
                                                                                       
                  
                                 
                        

                                                                 

                                                    
                                                      
                                                                                    
                        
              
                                                                                         
                                                                      
         
                                             

                                                    
                                                      
                                                                                    
                        
              
                                                                                         
                                                                      
         
                                             

                                                                                 
                                                                        
                                      
             
                                                                   
                             
                                                                                     
                 

                                                                                 
                                                                        
                                      
             
                                                                   
                             
                                                                                     
                 

                                                                                    
                                                                                       
                                                   
                                                                                              
                                                     
                                                                    
                                                       
                              
                                   
                                   
                                                                                          
                                                                                         
                                    
                                       
              
       

                                                          

                                                                           
                                               
                                                 
                                              
                                
                                  
                                                                                           
                                                                           
              
                                                                                
                        
                                                
                                            
                                            
                                                                           
         
                                                       
                                                                
                                                                                          
                                               
         
                              
                  
                                                               
                                         
                    
           
                                            
                                           
                                                  
                                                                              
                                                            
          

                                                                                 
                             
                                 
            
                                         
                                                            
                                              
                                                       
                                                       

                                                                          
def fresh (b : Fin 4) : BV L := (b, Fin.last (L + 1))

                                                                                  
               
                                            
                                                                                   
                                                          
         

                                                                              
                                                                                     
                                                          
                                                                      

                                                                              
                                                                                     
                                                          
                                                                      

                                                                                        
                                                                               
                                                                                        
                                                                                           
                                                                                         
                                                                    
                                          
                                                                            
                                                                   
                                                                                 
                             
                                                                               
                                                                               
                                                          
                                                                    
                                                                                      
                              
                                                        
                      
                                               
                        
                                                                             
                                                                             
                                                                                           
                                              
                                                                       

end BridgeControl

/-! ### Star control: the coherent-transformer source is not certified -/

namespace StarControl

open CoherentTransformer CoherentTransformer.Refutation CoherentTransformer.BipartiteLinkHost

variable (L : ℕ)

                                                                      
                                                                
                                

                                                        
                                           
                                                                                               
                                        
                                                                      
     

                                                                            
                                       
                                                                                           
                                                     
                                  
        

                                       
                                              
                                                                                               
                                                     
                                              
                           

                                                                                             
                                             
                                                                                       
                                                                                    
                                                 
                                       
                  

end StarControl

/-! ### Item-5 control: two modes do not force equal part-pair counts -/

namespace CountControl

/-- Parts of six vertices: `{0, 1, 2}` is a `001` triangle, `{3, 4, 5}` a `011` triangle. -/
def cp : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

/-- A single `001` triangle. -/
def P : Finset (Sym2 (Fin 6)) := triEdges {0, 1, 2}

/-- A disjoint `011` triangle. -/
def Q : Finset (Sym2 (Fin 6)) := triEdges {3, 4, 5}

theorem hasDecomp_single {V : Type*} [DecidableEq V] {p : V → Fin 2} {s : Finset V}
    (h : IsTypedTri p F0 s) : HasDecomp p F0 (triEdges s) :=
  ⟨{s}, by simpa using h, by simp, by simp⟩

                                                                                          

                                                                                          

                                                 
                                                                         

                                                 
                                                                         

                                               
                                       
                                                                                    
                                               

                                                                                      
                                                              
                                                                     
                 
        

end CountControl

end PartitionedTriangleAbsorption.SignedCertificate
