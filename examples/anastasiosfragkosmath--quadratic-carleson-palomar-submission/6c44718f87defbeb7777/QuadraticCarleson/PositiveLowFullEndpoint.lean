/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.PositiveLowFullMajorant
import QuadraticCarleson.PositiveLowFullIntegral

/-!
# The full-operator low endpoint branch

The actual low kernel acts on the genuine countable level-atom sum. Off the
union of the fivefold intervals, a common measurable majorant bounds every
real modulation simultaneously. Markov's inequality is applied only to that
majorant, giving an outer-measure bound without assuming measurability of
the real supremum. The exceptional set contributes at most five times the
sum of the interval lengths.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveLowFullEstimate

open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

                                                               
                                       

                                                                                      
                                                 
                                                  

                                                                       
                                                                 
            
                       
                          

                                                                                  
                                                                               
                                                
          
          
                                                                            

                                                                                  
                                                                              
                                      
                                                                                   
                            
          

                                                                        
                                 
                                                                  
                                   
                                                   
                                                  

                                                                      
                                                        
                                     
                                                                         
                                                   
                                                                    
                            
         
                                                                               
                                               
                            
         
                                                                          
                                   
                                                              

                                                                    
                                                          
                                                                                  
                                     
                                                                           
                                                                               
                                                                                     
      
                                                                            
                             
                                                                                                 
                                                                       
                                           
                                                                 
                                                                                              
                                                                

                                                                
                                                                            
                                                                   
                                                                                  
                                     
                                                                           
                                                       
                                           
                                                                                       
                                                          
                                                                          
              
                                                
                     
                                                                                                 
                                 
                                    
                         
                                                                                          
                                                                     
                                          
                                                                      

                                                                    
                                                                          
                                                              
                                                                                  
                                     
                                                                           
                                                       
                                        
                                                                                       
                                                                                               
                                                              

end PositiveLowFullEstimate
end QuadraticCarleson
