-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianObservationCoercivity
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Basis.Prod

/-! Exact actual pair Gram blocks and their Schur determinant. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function Module GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

                                                                            
                                                                                           
                                                                                              

                               
                                                                                   
                                                         
                                                             
                                                                  
                          
     

                               
                                                                                    
                                                         
                                                             
                                                                  
                          
     

                               
                                                                                    
                                                                                            
                                                                                   
                                                
         
                
                                        
                                        

                               
                                                                                     
                                                                                            
                                                                                   
                                                
         
                
                                        
                                        


                                                             
                                                                              
                                                              
                                                                                    
              

                                                              
                                                                              
                                                              
                                                                                    
              

                                                                             
                                          
                                                           
                                                                                                
                       
                                                                     
                                                                               
                                                                               
                                                                           
         
                               
              
            
                
              
                                                           
                                                             
                                                                                                    
                         
                                                                   
              
                                                            
                                                             
                                                                                                                
                         
                                                                   
            
                
              
                                                            
                                                             
                                                                                                                
                          
                                                                   
              
                                                             
                                                             
                                                                                                    
                          
                                                                   

                                                                     
                                                                             
                                                                    
                                                
                                                  
                                 
                               
                                                                                                     
           
                                
                                                                              
                                                                              
                                                                                                   
                                                                                    
                                                      
                                                                
                                   
                          
                                                       
                                                         
           
                                                                   
                                                                                    
                          
                                            
                                                                                                           
                                                                                                     
                                                                                         
                                                            
                                                
                                                          
                                                                                                      
                                                             
                                               
         
       

end
end SlowEquilibration.GaussianObservationCoercivity
