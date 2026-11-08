-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegression
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-! # Dimension-independent coercivity of true observation Gram operators -/
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

                                                                   
                                                         
                                    

                                            
                                                                 
                                                             
                                                      

                                                      
                                                                    
                                       
                 
                       
                                             
                           
                  
                                                                        
                                                 
                    
              
                                             
                                                       
                                              
                                                        
                                               
         
                          
                        

                                               
                                                          
                                               
                                                  
                                                               
                                                         
                                             
             

                                                    
                                                 
                                                     
                                                                                      
                                                             
         
                                                                                     
                                                                         
            
                                                                            
               
      
                                                    
                            

                                                              
                                                 
                             
                                                                                       

                                                                               
                                                                 
                                                    

                                                         
                          
                                                                     
                         
         
                                                          
                                                                                        
     

                                                             
                                                                              
                                                                                           
         
                                                                        
                       
                       
                                                               
                                 
                             
                                                 
        
                                                                     
                                    
                                                                                                
                         
                      
                                                                       
                                         

                                                               
                                                                              
                                                                         
                                                                            

                                                                         
                                                                              
                                         
                                                                     
                                                                                     
                    
            

end
end SlowEquilibration.GaussianObservationCoercivity
