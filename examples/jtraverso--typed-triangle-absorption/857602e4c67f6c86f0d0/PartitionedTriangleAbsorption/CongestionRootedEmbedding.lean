/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootedTemplateEmbedding
public import Mathlib.Data.Fintype.Fin

/-! # Rooted embeddings avoiding external auxiliary congestion

Roots may belong to the excluded set. Only newly embedded nonroots avoid it.
The exclusion is fixed during one template, since injectivity prevents a vertex
from receiving two auxiliary uses in that template. This is not yet the
simultaneous edge-degree induction for a whole family of private absorbers.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CongestionRootedEmbedding

open Finset RootedEmbeddingSelection RootedTemplateEmbedding AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- Verification of a prefix update, independently of how the new image was selected. -/
theorem update_prefix (T : SimpleGraph (Fin m)) (G : SimpleGraph V)
    (B : Finset (Sym2 V)) (k : ℕ) (hk : k < m) (f : Fin m → V)
    (hf : PrefixEmbedding T G B k f) (w : V)
    (hneq : ∀ i, i.val < k → f i ≠ w)
    (hparent : ∀ i, i.val < k → T.Adj i ⟨k, hk⟩ →
      G.Adj (f i) w ∧ s(f i, w) ∉ B) :
    PrefixEmbedding T G B (k + 1) (Function.update f ⟨k, hk⟩ w) := by
  let j : Fin m := ⟨k, hk⟩
  let g := Function.update f j w
  have hkeep : ∀ i, i.val < k → g i = f i := by
    intro i hi
    have hij : i ≠ j := by intro h; subst i; exact (lt_irrefl k) hi
    exact Function.update_of_ne hij w f
  have hnew : g j = w := Function.update_self _ _ _
  change PrefixEmbedding T G B (k + 1) g
  refine ⟨?_, ?_⟩
  · intro i l hi hl hil
    by_cases hiold : i.val < k
    · by_cases hlold : l.val < k
      · exact hf.injective i l hiold hlold (by simpa [hkeep i hiold, hkeep l hlold] using hil)
      · have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        subst l
        exact False.elim (hneq i hiold (by simpa [hkeep i hiold, hnew] using hil))
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      subst i
      by_cases hlold : l.val < k
      · exact False.elim (hneq l hlold (by simpa [hkeep l hlold, hnew] using hil.symm))
      · exact (Fin.ext (by dsimp [j]; omega) : l = j).symm
  · intro i l hi hl hil
    by_cases hiold : i.val < k
    · by_cases hlold : l.val < k
      · simpa [hkeep i hiold, hkeep l hlold] using hf.edges i l hiold hlold hil
      · have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        subst l
        simpa [hkeep i hiold, hnew] using hparent i hiold hil
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      subst i
      have hlold : l.val < k := by
        by_contra h
        have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        exact T.irrefl (hlj ▸ hil)
      obtain ⟨he, hb⟩ := hparent l hlold hil.symm
      refine ⟨?_, ?_⟩
      · simpa [hnew, hkeep l hlold] using he.symm
      · simpa [hnew, hkeep l hlold, Sym2.eq_swap] using hb

                                                                             
                                                                                 
                                    
                                                       
                                                    
                                      
                                                                         
                                                                         
                                                                                        
                                          
                                                        
                          
                                                                     
                          
                                                                
                                                      
                                                    
                                                                              
                                                           
                                                                           
                                                                       
                                    
                                                                  
                                                            
                                            
                 
                                                                         
                                                                                 
                  
                                       
                                                    
                              
                                                                                      
              
                                                                   
                                       
                                                  

                                                                                         
                                                                                       
                                                                                 
                                    
                                                       
                                                    
                                      
                                                                         
                                              
                                             
                                      
                                                                            
                                    
                                                                           
                                                                  
                                          
                                                      
           
                    
                                                                               
                  
                  
                                                   
                                      
                                                                                         
                                                                
                                                               
                                                                
                     
                                     
                                                   
                                                                                 
                                     
                                                      
                                                                     
            
                                                                       

                                                                                    
                                                                                          
                                                                                 
                                    
                                                       
                                                    
                                                                          
                                                                       
                                     
                                              
                                             
                                      
                                                                            
                                                                         
                                                       
                                                    
                                                
                                                                      
                               
                                                                                    
                                                                            
                                            
                                                                                        
                                                                 
                          
            
                        
                                                       
                                                                       
                                                                         

                                                         
                                            

                                                                 
                                 

                   
                                                                             
                                                                        
                                                      
                                                    
                                                                           
                        
                                   
                                                          
                                                                
               
                                               
       

                   
                                                                 
                                                          
                                            
         
                     
                                                                                   
                                                                              

                                                            
                                                                 
                                          

                                                                                          
                                                                                         
                                                                                       
                                                                                 
                                    
                                                       
                                                    
                                                                          
                             
                                                                       
                                     
                                              
                                             
                                      
                                                                            
                                                                         
                                                   
                                                                
                                                            
                                     
                                                                                   
                                                               
                                                                                  
                                                                         
              
                                          
                                           
                                                         

end PartitionedTriangleAbsorption.CongestionRootedEmbedding
