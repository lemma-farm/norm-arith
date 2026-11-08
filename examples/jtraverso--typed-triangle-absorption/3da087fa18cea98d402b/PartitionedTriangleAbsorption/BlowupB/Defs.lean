/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import Mathlib.Algebra.Module.BigOperators

/-! # BlowupB.Defs — physical (lattice) divisibility for arbitrary families of partitioned triangles

New module of the "Theorem B (blowup)" route. It only adds files; nothing in the existing tree is
modified.

The aggregate divisibility `IsIntDiv` (Definition 13.5) only sees the edge-count vector and the
degree vectors. The absorber machinery needs the stronger **physical** condition: the indicator of
the edge set is an integer combination of indicators of *actual* `F`-copies of `G`.

* `PhysCert p F G E T c` — copies `T j` of `F` in `G` and coefficients `c j` with
  `ind E = ∑ j, c j · ind (E(T j))` at every edge coordinate;
* `PhysDiv`, `PhysDivCost` — existence of a certificate, of cost `∑ |c j|` at most `w`;
* `physCert_of_isDecomp` — a decomposition is a certificate with unit coefficients;
* `isIntDiv_of_physCert` — physical ⇒ aggregate. The converse, on nearly complete blowups, is
  the per-family certificate lemma (`class_lattice_certificate` for `F3`), to be generalized in
  later modules of this route.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- Integer indicator of an edge set. -/
def indZ (E : Finset (Sym2 V)) (e : Sym2 V) : ℤ := if e ∈ E then 1 else 0

                    
                                                                                     
                 
 
                    
                                                                                         
                 
 
                                                                                         
                                                                                              
                                                                                 
                                                                                           
                                                                                 
 
                                                                            
                                                                                
                                    
                                                                                    
 
                                                                     
                                                                                    
                                            
                                                               
                                          
 
                                           
 
                                                                                          
                              
                                                                             
                                                                                           
                                                      
                                                                      
                               
                                    
                        
                      
                                   
                                           
                                                        
                                                      
                   
                                                 
                   
                   
                                           
                                 
                                                      
                                                 
                        
                        
                       
                     
                       
                                                   
                                                
                                   
                      
                           
                  
                                                                      
                                                       
                                                  
                                             
                           
           
                               
                
                         
                
                                                    
 
                                
 
                                                                     
                                                                    
                                                    
                 
                                                                                  
 
                                                                 
                                                                           
                                                          
                
                                                                                  
 
                                                                                    
                                                                             
                                                                                         
                                                                  
                           
                                                                   
                                                               
                                                                         
                             
                                             
                         
                                              
                                                                                
                                                                                             
                                                                                       
                           
                                              
                         
                                                                        
                                                                          
                              
                                               
                           
                                                                                            
                                                                                          
            
                                            
                                                                        
                                                                   
                                                                              
                                                                          
                                
                                                                               
                                              
                                        
                                               
                                            
                       
 
                                                                   
                                                                                                
                                                                       
                               
                                
 
end PartitionedTriangleAbsorption.BlowupB
