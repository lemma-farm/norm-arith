-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedObservationBlocks
public import SlowEquilibration.PairGradientNondegeneracy
public import SlowEquilibration.ObservationTargetEquiv
public import SlowEquilibration.GaussianResidualCoercivity

/-! Exact isometric regrouping of the actual mixed pair into its score and
gradient blocks. This preserves the canonical whole-field posterior at every
target and transfers the actual uniform observation coercivity. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity ObservationTargetEquiv
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

                                                                                     
                                                                                                
                                                                                           
                                                                                     

                                                                          
             
                                                                                 
                                                                            
                                                                                 
                                                                            

                                                                                  
             
                                                                                 
                                                                            
                                                                                 
                                                                            

                                                                             
                                                                

                                                                               
             
                
                                                                                   
                                                               
                                                                                   
                                                                
                
                                                                                   
                                                               
                                                                                   
                                                                

                                                                                       
                                                      
                                          
                                                                     
                                                               
      

                                                                              
                                                                                      
                  
                                                  
                                 
                                
                                   
                                   

                                                             
                                                 
                                                         

                                                                    
                                                                                     
                                                        

                                                                         
                              
                                                                                                           
                                                                                       
       
     

                                                                               
                                    
                                                                                                              
                                                            
         
                                                                                                  
                                                                                                                                                 

end
end SlowEquilibration.NormalizedPairObservations
