/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.Semigroup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

/-!
# Operations on strongly continuous semigroups

This file provides the two constructions used in the diagonal-diffusion step of Lemma 2.2:
multiplication by a real exponential and finite coordinatewise products.
-/

open scoped NNReal

noncomputable section

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

section Conjugate

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Transport a strongly continuous semigroup through a continuous linear equivalence.  This is
the abstract conjugation step used when the paper returns from diffusion eigenvector coordinates
to the original state space. -/
def conjugate (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) : C0Semigroup ℂ F where
  toFun t := (e : E →L[ℂ] F).comp ((S t).comp (e.symm : F →L[ℂ] E))
  map_zero' := by
    ext x
    change e (S 0 (e.symm x)) = x
    simp
  map_add' s t := by
    ext x
    change e (S (s + t) (e.symm x)) =
      e (S s (e.symm (e (S t (e.symm x)))))
    rw [S.add_apply]
    simp
  strongContinuous' x := by
    change Continuous fun t : NNReal ↦ e (S t (e.symm x))
    exact e.continuous.comp (S.strongContinuous (e.symm x))

       
                                                             
                          
                                                 

                                                                                   
theorem norm_conjugate_le (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) (t : NNReal) :
    ‖S.conjugate e t‖ ≤ ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
  calc
    ‖S.conjugate e t‖ ≤
        ‖(e : E →L[ℂ] F)‖ * ‖(S t).comp (e.symm : F →L[ℂ] E)‖ :=
      (e : E →L[ℂ] F).opNorm_comp_le _
    _ ≤ ‖(e : E →L[ℂ] F)‖ *
        (‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖) := by
      gcongr
      exact (S t).opNorm_comp_le (e.symm : F →L[ℂ] E)
    _ = ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
      rw [mul_assoc]

                                                                                               
                                                                          
                                           
                       
                                                            
      
                       
                                                             
                             
                                                            
            
                                                              
          

end Conjugate

                                                                                 
                                                                        
                                               
                 
                                                                          
                     
                    
         
                                                                      
                                    
                                                  
                    
                                                           
                           
                                                                       
                                                                              
              
                                                                           
                      

       
                                                                                 
                                                                        

                                                        
                                                                           
                                                                 
      
                            
                                                 
                                            
                                            
                                                                           

                                                                               
                                               
                                                                       
                                                         
      
                                                              
                                  
                                        
            
                
                                           

section Pi

variable {ι : Type*} [Fintype ι]
  {X : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
  [∀ i, CompleteSpace (X i)]

                                                                       
                                                                      
                                                    
                 
           
                                
                    
           
                                   
                           
                                                            

       
                                                                           
                                             

                                                                                            
                                                              
                                                 
                      
                                                
         
                                                                    
         
      
                                                              
                     
                                                                     

end Pi

end C0Semigroup

end
