module

public import RequestProject.Euler.BanachLocalRemainder
public import RequestProject.Euler.BanachSequenceGreenIdentity

/-! Actual weighted nonlinear remainder sequences on a closed Banach
ball. The exponential weights cancel in the Lipschitz estimate, so the
true local small constant is retained in the complete sequence space. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_weight_inverse_pow_facts {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℕ) :
    0 ≤ ρ ^ n ∧ 0 ≤ (ρ⁻¹) ^ n ∧ (ρ⁻¹) ^ n ≤ 1 ∧ ρ ^ n * (ρ⁻¹) ^ n = 1 := by
  have hp : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : ρ⁻¹ ≤ 1 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) zero_lt_one hρ
    simpa only [one_div, div_one] using h
  refine ⟨pow_nonneg hp.le n, pow_nonneg hi0 n, pow_le_one₀ hi0 hi1, ?_⟩
  rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]

                                                                                  
                             

                                                                       
                                         
                                                
                                               
                                                                                                
      
                                                                        
                                                                                           
               

                                                                          
                             
                                                                   
                                
                                                          
                                                                                       
                       
                                               
                                                                                            
                                         
      
                                                            
                               
                                                                    
                                                                      
                             
                                                                        
          
                                                              
                                          
                                                
                                                               

                                                                                        
                                                               
                                            
                                             

                                                                      
                                                         
                                                                   
                                
                                         
                                                            
                                                                        
                                          
                                                                       

                                                     
                                                         
                                                                   
                                
                                               
                                                        
                                                          
             
                                                                                                      
                                                                                      
                                          

                                                               
                                                         
                                                                   
                                
                                             
                                                                                                      

                                                                 
                                                         
                                                                   
                                
                                     
                                                                      
                                                                                                  
                                                                                   
         
                                                                          

                                                                     
                                                         
                                                                   
                                
                                       
                                                                                                   
                               
                                                                                                  
                                                                                                  
                                                                                             
         
                                                                                 

end Euler2D

end
