module

public import Mathlib
                                                  

@[expose] public section

/-!
# The open cone of uniformly positive symmetric operators

The positivity margin is an explicit quadratic-form bound. It implies the
strict positive definiteness required by the LMI. This cone is open and convex
and contains the identity, so it can be used in the proved separation theorem.
-/
noncomputable section
namespace LinearStochastic.PositiveCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Positive definiteness with a uniform quadratic-form margin. -/
def UniformPositive (T : E →L[ℝ] E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * ‖x‖ ^ 2 ≤ inner ℝ (T x) x

                                                                      
                                                    
                             
                                                                                    

                                                                               
                             
         
                                   

                                                                            
theorem uniformPositive_of_norm_sub_lt (T S : E →L[ℝ] E) (ε : ℝ)
    (hε : 0 < ε) (hT : ∀ x, ε * ‖x‖ ^ 2 ≤ inner ℝ (T x) x)
    (hclose : ‖S - T‖ < ε) : UniformPositive S := by
  refine ⟨ε - ‖S - T‖, sub_pos.mpr hclose, ?_⟩
  intro x
  have hinner := neg_le_of_abs_le (abs_real_inner_le_norm ((S - T) x) x)
  have hop := mul_le_mul_of_nonneg_right ((S - T).le_opNorm x) (norm_nonneg x)
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hinner hop
  nlinarith [hT x]

                                                                             
                                                                       

                                                   
                                  
                                          
                                                               

                                                  
                        
            
                              
                    
            
                                                              
                                                

                                                    
                               
                          
                          
                                     
                        
             
                                 
                    
                                                                
                                        
              
                                  
         
                                                                          
                                                                           
                                         
                                                
                                                
           

                                                                    
                                                            
                                                                                    
                                          
                                           
                                                                              
                                                             
                                                    
                                                                          

end LinearStochastic.PositiveCone
