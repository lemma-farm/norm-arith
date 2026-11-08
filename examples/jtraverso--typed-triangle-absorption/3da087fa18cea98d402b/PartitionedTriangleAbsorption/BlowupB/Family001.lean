/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Darts
public import PartitionedTriangleAbsorption.BlowupB.LinearExtras

/-! # BlowupB.Family001 — absorbers for the type `{0, 0, 1}`

The family `F001 = {{0, 0, 1}}` (two vertices in class `0`, one in class `1`) is neither linear
(`not_isLinearFam_001`) nor satisfies `ThreeStepLinks` (`not_threeStepLinks_001`: the link of
class `0` is the single edge `0 — 1`, bipartite). It is covered here by the dart construction:

* integral divisibility gives, at a class-`0` vertex, as many class-`0` as class-`1` neighbours,
  and at a class-`1` vertex an even number of (class-`0`) neighbours;
* pair them (`0`-edges with `1`-edges, resp. arbitrarily) and follow the darts: the classes along
  a trail read `0, 0, 1, 0, 0, 1, …` in one direction or the other; the phase of a dart is read
  off its two classes, the centre class is `0`;
* `phasedTrail_of_pairing` gives phased trail systems (`phasedDiv_001`), and
  `phased_terminal_absorber` the terminal absorber (`terminal_absorber_001`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv TypedTransformer

universe u

section Count

variable {V : Type u} [Fintype V] [DecidableEq V] {t : ℕ}

                                                                                             
                                                                                  
                                 
            
                                                              
                                        
                                               
                                         
              
                                 
                 
                    
                   
                      
                                                       
                          
                     
                                            
              
                                 
                               
                    
                   
                      
                                                       
                     
                          
                                            
                             
                                             
                 
                   
                      
                                                       
                     
                     

                                                                              
                                                                                        
                         
                                                                                  
                                                                           
                                                                      
                                                                   
           
                                                         
                                             
                                                                         

end Count

section Involutions

variable {V : Type u} [DecidableEq V]

                                                                       
                                                                                        
                                                                                          
                                         
                                                                          
                                                                                            
                   
              
                                                
                                                                      
                                                    
                                                                                            
              
                                                          
                                                          
                                                                 
                                                                                            

                                                                        
                                                             
                                                               
                                                                                   
                                        
                                      
                        
         
                                                                             
                            
                      
                                
                                                                                        
                                                   
                                
                                                            

end Involutions

                                
                                                   

                                                            
                                 
        

                                                      
         
                                          
             
        

                                                     
                        
                                
          
            
        

                                                                     

                          
                                                                        
                                                         

                          
                                                                                             
                                                         

section Pairing001

variable {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin 2} {P : Finset (Sym2 V)}

                                                                                                   
                                                       
                                                                                     
                            
                          
                                                  
            
                                
          
                                                          

                                             
def nbr (p : V → Fin 2) (P : Finset (Sym2 V)) (v : V) (j : Fin 2) : Finset V :=
  univ.filter fun u => s(v, u) ∈ P ∧ p u = j

                                                                                     
                                                                      
                                                                           
                                                                         
                                     
                                                                
                                        
                                      
                                                   
                            
                            
                                             
                                                            
                                                                  
                                                           
                        
                    
                                      
                                       
                 
                                
                                                           
                              
                                          
                                                                        
                                  
                                     
                                                                                             
                                       
                                                         
                                                                        
                                  
                                     
                                                                                             
                                       
                                                         
                                                                                  
                            
                                          
                                                        
                                                             
                                                
                
                                        
               
                            
                          
                                        
                                             
                              
                                                                            
                                   
                                    
                                                       
                                            

                                                
                                                                                 
                                                              
                                                                                               
                                                      
                                                                                   
                                  
                                                                       
                                   
                                                           
                                   
                                                                   
                     
                       
                       
                             
                                        
                                                                             
                                           
                 
                                           
                                                                                 
                                   
                                                
                                                                  
                 
                                  
                              
                                                       
                                  
                                           
                 
                                        
              
                    
                 
                                           
                                                                                 
                                   
                                                
                                                                  
                 
                             
                                        
                                                 
                                           

end Pairing001

                                                                               
                                                                                      
                                                      
                                                            
                                         
                                                                                   
                                                                                 
                                            
                                                           
                                                               
                                                                           
                                                     
                                                                               
                                                                        
                                                     
                                                                                    

end PartitionedTriangleAbsorption.BlowupB
