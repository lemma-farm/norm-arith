/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Universal
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-!
# Universal absorbers for every family with a trivial lattice

`TrivialLattice F`: on loopless active edge sets, ordinary divisibility (`Even3`) already implies
`IsIntDiv p F`. For such F with `ThreeStepLinks`, common neighbour classes, and an explicit
witness bound `B` for 42-edge pieces with terminal order and size `≤ 2^21`, the ORDINARY refiner
gives `UniversalCert F`. The proof is the F* argument with F as a parameter.
-/

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12

universe u

/-- Trivial lattice: on loopless sets, F-divisibility is ordinary divisibility of active sets. -/
def TrivialLattice (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V)),
    (∀ e ∈ E, ¬ e.IsDiag) → (IsIntDiv p F E ↔ ActiveEdges F p E ∧ OnePart.Even3 E)

                                                                  
                                                                   
                                                                      
                                                               
                                                                        
 
                                                                    
                                                                       
                                                                              
                                                               
                                                                                  
                                             
                                                               
                         
                                                       
                                                                                       
                                                        
                               
                                                                      
                                                                           
                                 
                                                    
                                                                        
                                                                                
                                           
                                                                                             
                                        
            
                                                      
                                                       
                              
                                        
                           
                
                                                         
                              
                              
                    
                                              
                                                               
                                                    
                                                                             
                         
                                                           
                       
                                                                     
                                                                    
                                                                              
                                                                                    
                                                                           
                                                    
                                                                                   
                                                                                             
                                                   
               
                                                                            
                                                  
                                                                        
                                                             
                                                                                      
               
                                 
                                                                                 
                                                   
                                            
                                                          
                                            
                
                                                                                        
               
                                           
                 
                                      
                 
                                                                       
                 
                                                  
                                                                                               
                 
                                                                                        
               
                                         
                      
                                                                               
                 
                                                                               
                                                                    
                                                                             
                                                                            
                                                    
                                                           
                                                            
                                                                                         
                     
                                          
                                                                
                                                                  
                                                                    
            
                                          
                                                                                                  
                                                                                  
                                
             
                                                                                                
            
                   
                                                                 
                     
                                                                                        
                
             
                                                                 
                                                                                       
                     
                                                                                             
                                         
               
             
                                                             
                                             
                                                                 
                                                             
                                                                         
                                  
                                         
                                                                         
                                                
                                            
                                                                                      
                                                                                                 
                                                       
                                                                     
         
                                                                                 
                 
                                                                              
                                        
                                                                                               
                        
                                       
                                                                                   
                                                                             
                                                                        
                                         
                                     
                                                                      
                                                                
                                                       
                 
 
                                                                                                     
                                                                 
                                                                       
                                                                              
                                                               
                                                                                  
                          
                                      
                                                                             
                                                                                 
                                                                                     
                                                                               
                                                                        
                                                                                     
                                                                                             
                                                                                     
                                                                                              
                                     
                                          
                                                                                    
                                                              
                                                                                    
                                                                                                
                 
 
                                        
                                                                             
                                                                                                 
                                                                                         
                                                                                             
                                                                                      
 
                                       
                                              
 
end PaddedGeneral
