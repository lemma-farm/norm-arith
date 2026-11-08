/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Fibre
public import PartitionedTriangleAbsorption.TypedCatalystBridgeStage93

/-! # Selecting target triples of actual original tokens

Nonnegative type coefficients specify a disjoint family of abstract triangle
slots. The accepted fibre equivalence matches these slots to actual original
edges. This constructs their partition into target triples, including repeated
labels. The insertion invariant then transports the assignment to the current
physical token positions. No physical cut or terminal decomposition is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TargetTripleSelectionStage95

open Finset ColouredHub CatalystInsertionStage89

variable {t : ℕ} {V : Type*}

abbrev Slots (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℕ) :=
  Tri F c × Fin 3

/-- Read the actual finite original edges as the accepted fibre vector. -/
theorem edgeVec_eq_vecOf (p : V → Fin t) (Y : Finset (Sym2 V)) :
    vecOf (fun e : Y => Sym2.map p e.val) = edgeVec p Y := by
  classical
  have hpair (e : Sym2 V) : pv (Sym2.map p e) = pairVec p e := by
    induction e using Sym2.ind with
    | _ u v => rfl
  unfold vecOf edgeVec
  simp_rw [hpair]
  exact Y.sum_coe_sort (fun e => pairVec p e)

                                                                         
                                                                            
                                                               
                                                              
                              
                                                               
                               
                                                                      
           
                                              
                                                 
                                               
                                        
                                

                                                                    
                                                       
                                                    
                                                             
           
                                                   

                                                                             
                                                             
                              
           
                                     
        
               
                                          
                              

                                                                               
                                                             
                       
           
            
                                       
                          

                                                                                  
                                                                             
                                          
           
                    
               
                                      
                                      
                                                         
                                  

                 
                                                                               
                                               
                                    
           
       
             
            
                                          
                             
            
                                             
                         
                                                             
                                 

                                                                          
                                                                     
                                                                    
                                                           
                                                        
                                 
            
                                                    
                                         
                                                      
                               
                                             

section Inserted

variable [Fintype V] [DecidableEq V]
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)}
variable {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
variable {U : Finset (Sym2 V)} {Z : Finset V}

                                                                       
                                                              
                                             
                                                                     
               
                                         
                                           
                                                
                                    

                                                                             
                                                             
                                                              
                                                                         
                                                                         
                
                                                          
                                                                
                                                                  
                                              
                                                                 
                                                                   
                                              

                                                                     
                                                                         
                                                                            
                                                            
                                           
                                                         
                                                                 
                          
                                                            
                                          
                                                                 
                                                         
                                           
           
                                                      
                                                                            
             
                                                               
         
               
              
                                           
                                                          
              
                                          
                                          
                                                                                               

                                                                   
                                                                        
                                                                    
                                           
                                                         
                                                                 
                                                 
                                                       
                                                      
                                                 
                                                              
                                           
                                                                 
                                                         
                                           
           
                                                                      
                                    
                                                     
                                    
                                              
                                                                  
                                                                             
                                                                                           
                                                      
                                      
                                                             
                 
                                                        
                                   

end Inserted

end PartitionedTriangleAbsorption.TargetTripleSelectionStage95
