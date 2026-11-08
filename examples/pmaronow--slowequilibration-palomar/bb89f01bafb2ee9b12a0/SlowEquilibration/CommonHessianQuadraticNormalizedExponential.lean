-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianQuadraticExponential

/-! A dimension-uniform normalized exponential bound for actual weighted
Gaussian square fluctuations, with either sign of every spectral weight. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

                                                                        

                                                                               
                                                                                       

                                                                      
                                                                                     
                                                                         
                                                    
                                                       
                                                                    
                                                                     
                                                                        
                                                                             
            
                       
                                      
                                           
                                                       
                                        
                                                                             
                                           
                                             
        
                                                                         
                       
                                   
                                   
                                                
                                                         
                                                                                             
                                           
        
                                                                                                                           
                                                                          
                                                    
        
                                                                             
                     
                                                
                                                        
                  
                                                           
                                                                 
                                                                             
                                                                               
                           
                                  
                                                                                                             

end
end SlowEquilibration.GaussianQuadraticVariance
