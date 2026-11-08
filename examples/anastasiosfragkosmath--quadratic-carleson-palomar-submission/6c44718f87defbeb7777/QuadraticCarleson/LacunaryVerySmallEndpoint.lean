/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.LacunaryVerySmallOperator
import QuadraticCarleson.FiniteModulationKernelComparison

/-!
# The canonical lacunary very-small endpoint estimate

The actual sum of very-small scale outputs is estimated by Markov on the
complement of the canonical fivefold exceptional set. The exceptional set
costs at most five times the input L¹ mass. Since the stopping decomposition
is normalized at height one, the general global threshold bound retains this
exceptional term; the paper uses the resulting threshold-one estimate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryVerySmallEndpoint

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate LacunaryVerySmallOperator LacunaryVerySmallRange

set_option autoImplicit false

                                                                             
                                               
                                                                               

                                                                                     

                                                
                                                                             

                                                                           
                                                                    

                                                                       
                                                  
                                                                                    
                                                                              
                            
                                         
                                                   
                          
                                                                              
                                                  

                                                                      
                                                                    
                                                              
                                                        
                                                        
                                                                    
                                                                           
                                                
                                                                          
                                                               
                                                          
                            
                                                                                             
         
                                                                                  
                 
                          
                    
            
                                                                 
                      

                                                                        
                                                                         
           
                                                        
                                                        
                                                        
                                                                   
                                                        
                                                                          
                                                             
                                  
              
                       
                     
                           
      
                                                      
                                                                         
                                                           
                                
                                             
                                                                                     
                                                                              
                    

                                                                        
                                   
                                                        
                                                        
                                             
                                                               
                                                    
                                                                
                                                                  

                                                                        
                                  
                                                    
                                                        
                                           
                                           
                                                               
                                                        
                                                                          
                      
      
                                                             
                                                                
                                                                        
                                
          
                                                                

                                                                            
                                               
                                                                  
                                                        
                                           
                             
                                                                   
                                                    
                                                                              
                            
                                                                               

                                                   
                                                                   
                                                              
                                                               
                                                 
                                                                                       

                                                                                 
                                                             
                                                                  
                                                      
                                       
                                                   
                                                                                   


end LacunaryVerySmallEndpoint
end QuadraticCarleson
