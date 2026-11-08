module

public import Mathlib
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Variational minima and source responses

Lax--Milgram constructs weak solutions on a real Hilbert space. Symmetry
then gives the exact affine and source objective gaps, including uniqueness
of the variational extrema. These are the functional-analytic steps used by
the finite-cutoff response construction and localized perturbation argument.
No Sobolev space or model response is postulated here.
-/

open InnerProductSpace
namespace SubdiffusiveProcess

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

                                                                               
                                                                
                                                              
                          
               
                                           
                                                                        

                                                                                   
theorem existsUnique_bilin_eq_load [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B) (L : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, B u v = L v := by
  let T := hB.continuousLinearEquivOfBilin
  let f := (toDual ℝ H).symm L
  refine ⟨T.symm f, ?_, ?_⟩
  · intro v
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (T (T.symm f)) v = L v
    rw [T.apply_symm_apply]
    exact toDual_symm_apply
  · intro u hu
    apply T.injective
    rw [T.apply_symm_apply]
    apply (toDual ℝ H).injective
    ext v
    change inner ℝ (T u) v = inner ℝ f v
    rw [hB.continuousLinearEquivOfBilin_apply, hu, toDual_symm_apply]

                                                                                              
                                                       
                                                       
                                     
                                                                   
                                
                         
      

                                                                               
                                                 
                                                             
                                                
                                           
                          
                           
                                
             
          

                                                                                      
                                                      
                                               
                                                   
                                         
                                               
                                              
                                   
                                                      
                                               
                              
                                
                                        
                                               
                                                      
                      
                            
                                                        
                                        
              
                         
                                       
                                
                                  
            
                                         
                                
                                                                          
                                 
                                                                      
              
                                       
                                                                
                             
            
                
                                          

                                                                                 
                                                       
                                               
                                                   
                                         
                                                                  
                                                                            
                             
            
                             
                                                                  
                                                 
                                                             
                                                               

                                                                
                                                
                                               
                                                   
                                                           
                                                 
                            
                                                                         
                             
                                                                 
                                                 
                                                             
                                                                             
                    

                                                                                               
                                                       
                                               
                                                 
                                                              
                                                      
                                            
                                         
                                
                                                                          
                                 
                    
           
                
                              
              
                                                               
                                                                 

                                                               
                                                
                                               
                                                       
                                                         
                              
                                                      
                                                
                                                         
                                                                             
                

end SubdiffusiveProcess
