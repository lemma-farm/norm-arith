import QuadraticCarleson.KrauseLaceyRemovedCarlesonMass
import QuadraticCarleson.KrauseLaceyPrunedPhysicalMaximal
import Mathlib
/-!
# Actual active-family pruning at an exponential cutoff

The source cutoff has size `O((s+1)2^s)`. At the explicit choice below
the exceptional measure is at most `2^(-8(s+1))` times the root length;
the total discarded interval length has the corresponding exponential
bound. The retained genuine physical maximal operator has the proved
linear-in-`s` Rademacher--Menshov loss.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

                                                     

                                                                     

                                                 
                                                             
                          
                                                                                  
       

                                                   
                                                                                  
                                      
                                                                       
      

                                               
                                                                          
                                                      
                                       
                                                            
                                                                              
                                 
                                       

                                                
                                                                                
                              
                                                          
                                                                                   
                                                                               
                                                                
                                          
                                                                
                                                        
                                                                   
                                                              
                                                    
                                                                                  
                                                        
                                       
                                                      
                                                                            
                                                                              

                                          
                                                                              
                              
                                                          
                                                                                   
                                                                               
                                                                
                                           
                                                                
                                                                    
                                                                         
                                                                              
                    

                                           
                                                                              
                              
                                                          
                                                                                   
                                                                               
                                                                
                                                                  
                                                                                               
                 
                                              
                                                                        
                                                                   
                                                              
                                                              
                                                                        
                                           
                                                    
                                                                                   
                        
                                                                           

                                            
                                                          
                                                             
      
                                       
                    

                                                 
                                                          
                                                                   
        
                                                                                       
                 
                                                      
                                        
                
                                          
                                                                                   

                                                           
                                                             
                                                       
                              
                                                          
                                                                                   
                                                                              
                                                                                 
                                                   
                                                                   
                                                
                                          
                                                               
                                                                               
                                                             
                                
                                                                              
                                                    
                                                                     


end KrauseLaceyBadScale
end QuadraticCarleson
