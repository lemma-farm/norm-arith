/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Assembly
public import PartitionedTriangleAbsorption.SignedHinge.Gadget
public import PartitionedTriangleAbsorption.SignedHinge.Wedge
public import PartitionedTriangleAbsorption.SignedHinge.Expansion

/-! # Occurrence data, slots, wedges and local blocks

`OccData` records, for every occurrence `o`, the roots `a b c` of its certificate triangle,
the apex `x` of the fresh copy `{a,b,x}`, the hinge `H` for `{a,b,c}, {a,b,x}`, and the two
further apices `y, z` supplied by `hinge_gadget`. Slot `(o,k)` has base edge
`ab, ac, bc` (`k = 0, 1, 2`), apex `x, y, z`, slot triangle `{base, apex}` and slot wedge
(the two apex edges). `OccGood` collects the facts proved by the selection and the gadget.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {O : Type*}

/-- Chosen data of all occurrence gadgets. -/
structure OccData (V O : Type*) where
  a : O → V
  b : O → V
  c : O → V
  x : O → V
  y : O → V
  z : O → V
  H : O → Finset (Sym2 V)

namespace OccData

variable (D : OccData V O)

/-- The non-root support of the occurrence hinge. -/
def fresh (o : O) : Finset V := vertSet (D.H o) \ {D.a o, D.b o, D.c o}

/-- First base vertex of a slot. -/
def bu (σ : O × Fin 3) : V := ![D.a σ.1, D.a σ.1, D.b σ.1] σ.2

/-- Second base vertex of a slot. -/
def bv (σ : O × Fin 3) : V := ![D.b σ.1, D.c σ.1, D.c σ.1] σ.2

/-- Apex of a slot. -/
def ap (σ : O × Fin 3) : V := ![D.x σ.1, D.y σ.1, D.z σ.1] σ.2

                                                           
                                                                                     

                     
def tri (σ : O × Fin 3) : Finset V := {D.bu σ, D.bv σ, D.ap σ}

/-- The local closure `Y o`: the occurrence hinge minus the four `y,z` wedge edges. -/
def core (o : O) : Finset (Sym2 V) :=
  D.H o \ {s(D.a o, D.y o), s(D.c o, D.y o), s(D.b o, D.z o), s(D.c o, D.z o)}

end OccData

/-- Facts about one chosen occurrence gadget. -/
structure OccGood (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (Z' : Finset V) (D : OccData V O) (o : O) : Prop where
  hab : D.a o ≠ D.b o
  hac : D.a o ≠ D.c o
  hbc : D.b o ≠ D.c o
  copy : IsCopy p F G {D.a o, D.b o, D.c o}
  roots : ({D.a o, D.b o, D.c o} : Finset V) ⊆ Z'
  adj_ax : G.Adj (D.a o) (D.x o)
  adj_xb : G.Adj (D.x o) (D.b o)
  part_x : p (D.x o) = p (D.c o)
  sub : ∀ e ∈ D.H o, e ∈ G.edgeSet
  hinge : IsHinge p F {D.a o, D.b o, D.c o} {D.a o, D.b o, D.x o} (D.H o)
  x_fresh : D.x o ∈ D.fresh o
  fresh_disj : Disjoint (D.fresh o) Z'
  ya : D.y o ≠ D.a o
  yb : D.y o ≠ D.b o
  yc : D.y o ≠ D.c o
  yx : D.y o ≠ D.x o
  za : D.z o ≠ D.a o
  zb : D.z o ≠ D.b o
  zc : D.z o ≠ D.c o
  zx : D.z o ≠ D.x o
  yz : D.y o ≠ D.z o
  triY : IsTypedTri p F {D.a o, D.c o, D.y o}
  triZ : IsTypedTri p F {D.b o, D.c o, D.z o}
  ay : s(D.a o, D.y o) ∈ D.H o
  cy : s(D.c o, D.y o) ∈ D.H o
  bz : s(D.b o, D.z o) ∈ D.H o
  cz : s(D.c o, D.z o) ∈ D.H o
  dec_core : HasDecomp p F (D.core o)
  dec_block : HasDecomp p F (D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)})

namespace OccGood

variable {G : SimpleGraph V} {Z' : Finset V} {D : OccData V O} {o : O}

                                                                                 
                
             

                                                                 
                                                                    
                            

                                                                 
                                                                    
                            

                                                                      
                                           

                                                                      
                                           

                                                                      
                                           

                                                                                      
                                  

end OccGood

namespace OccData

variable {G : SimpleGraph V} {Z' : Finset V} (D : OccData V O)

                                                                                             
                    
             
                       
                       
                       

                   
                                                                                        
                    
                           

                   
                                                                                        
                    
                           

                                                                                        
                    
             
                   
                   
                   

                                   
                                 
                                                                      
                    
                     

                                                                              
                            

                                                                              
                            

                                                                                  
                                     

                                                                                       
                                              

                                                                                       
                                              

                                    
                                              
                                                                               
                                        
                         
                      
                        
                   
            
               
                                                                             
                                                                                       
                                                
                   
           
                               
                                    
                               
                                    
                               
                                    
                                                   
                                                     

                                     
                                                                  
                                
                    
                
                                                                            
             
                                             
                                                        
                                                                              
                                         
                   
                                             
                                                                                 
                                             
                                                                                 

end OccData

end PartitionedTriangleAbsorption.SignedHinge

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {O : Type*}
  {G : SimpleGraph V} {Z' : Finset V}

namespace OccData

variable (D : OccData V O)

                   
                                                           
                                                                
                                                                          
                                               
       
                                                                      
             
                           
                                                                                        
           
            
                                               
                                                    
                                                
                                                
                                                
                                                
                                                
                                                

                                                                                      
                                                                                           
                
                                
       
                                                                   
             
                                                  
                     
                              
                              
                      
                        
                        
                        
                        
                         
                                                                                     
                             
                                  
                             
                              
                                       

                                                               
                                                          
                                             
            
                                     
                        
                                                        
                               
                                                      
                                            
                                               
                                                                          
          
                                           
          
                                           

                                                                 
                                                                                     
               
                
                                     
                                                                      
                
                  
                                                                                  
                                                              
                                                                
                                               
                            
                                                                   
                                                                   

                                                           
                                                                         
            
                                     
                        
                                               
                            
                        
                             

                   
                                                              

                                                                         
                                           
                    
                
                    
               
             
                                                                   
                                                                        
                                                                    
                                           
                
           
                                                                                 
           
                                                                  
                                                                
              
         

                                       
                                                        
            
                                          
                                                    
                                                                                 

                                                  
                                                                                
                                                            
                                                                               
                        
                                                   
                                  
                                      
                    
                
                                                        
                                                        
                                                  
                                                  
                                                  
                                                  

                                                                   
                                        
                                                                              
            
                                                    
                          
            
            

end OccData

end PartitionedTriangleAbsorption.SignedHinge
