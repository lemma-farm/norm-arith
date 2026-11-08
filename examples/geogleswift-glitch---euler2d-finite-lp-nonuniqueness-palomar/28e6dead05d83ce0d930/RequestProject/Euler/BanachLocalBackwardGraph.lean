module

public import RequestProject.Euler.BanachBackwardOrbitUniqueness

/-! A graph chosen from the actual weighted contraction has a unique
small backward orbit. Its shift identities follow from that uniqueness.
No smoothness or invariant-manifold theorem is used as an assumption. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure IsLocalWeightedBackwardGraph (F : E → E) (P : E →L[ℝ] E) (ρ r : ℝ)
    (x : E → ℕ → E) : Prop where
  backward : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ n, F (x ξ (n + 1)) = x ξ n
  norm_le : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ n,
    ‖x ξ n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖
  coordinate : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → P (x ξ 0) = ξ
  unique : ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ r / 2 → ∀ y : ℕ → E,
    (∀ n, F (y (n + 1)) = y n) →
    (∀ n, ‖y n‖ ≤ r * (ρ⁻¹) ^ n) → P (y 0) = ξ → y = x ξ

                                                         
                                                         
                                               
                                                                                    
                                                                         
                                     
                                                                         
                                                  
                                        
                                              
                                                              
                                                                
                                     
                                         
                                               
                                                 
                                          
                                          
                                                         
                                                 
                                             
                                                  
                                                                              
                                                                                        
                                          
                                                                    
                              
                                                  
                                     
                                           
                    
                
                             
                                                                                   
                                                                                          
                                                                 
                                                                     
                                                                               
                   
                                                                                 
                                                                       
                                                             
                                  
                                          
                                             
                                       
                                                                         
                                                            
                                                                 
                           
                                                         
                                            
                                        
                                              
                                        
                                                    
                                                                     
                                                  
                                    
               
                                                                          
                                                                                         
                                                                                      
                  
                             

namespace IsLocalWeightedBackwardGraph

variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

                                                                   
                                                                     
                                 
                            
                                            
                                              
                                 
           

                                                                   
                                          
                                              
                                   
                                              
      
                               
           
                                     
           
                                                 
                                                 
                                                                                 
        
                                   
                                                         
                                                          
                                                
                                                                
                        
       

                                                         
                                
          
                                                                                                  
                                                                            

                                                                  
                                          
                                              
                                                            
                                       
                                                                                 
      
                               
           
                
                 
                                           
           
                
             
                                        
                                                 
               
                                          
                                                               
          
                                                       
                                                 
                       
                                                                
                    
                  
                                                                          
       

end IsLocalWeightedBackwardGraph

end Euler2D

end
