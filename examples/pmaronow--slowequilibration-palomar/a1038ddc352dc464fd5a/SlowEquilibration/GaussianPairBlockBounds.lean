-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairGramSchurDeterminant

/-! Dimension-free operator bounds on genuine Hilbert-product covariance
blocks, and an actual independent product observation for comparison. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {E F G H I E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup I] [InnerProductSpace ℝ I] [FiniteDimensional ℝ I]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

                                                                       
                                   
                                                                    
                           
      
                                                           
                                          
            
                                          
                                             
                    

                                                                        
                                                                      
                                                              
                                     
                                                        
                                                                                       
                                                                    
                 
                                                                      
                                                             
                                                                                           
                                                                
                                                                
                                                                
                                                                
                                                    
                                                    
                                                    
                                                    
                                                                      
                                                              
                                                              
                                                              

                                                                               
                                                      
                                           
                                                                             

                                                                                                        
                                                                                    
                                                                

                                                                                     
                                                                                         
                         
         
                                                                                             
                                                                      
     

                                                                                        
                                                                                
                                                                                        
     

                                                                                                        
                                                                 
                                                                                    
         
                         
                         
                                                                                                                 

                                                                              
                                                          
                                                                      
                                                                                      
                                                                    
                 
                                                                                
                                                
                                                      
                                                                                                     
                                                                                                               
                                                                
                                                                   
                                            
                                                                                 
                                            
                                                                                 
                                 
                                 
                                                               
                                                                             
                                              
                                            
                                                              
                                                      

end
end SlowEquilibration.GaussianObservationCoercivity
