import QuadraticCarleson.KrauseLaceyNonstandardSignedSum
import QuadraticCarleson.KrauseLaceyGenerationRecombination
import QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface
import Mathlib
/-!
# The actual nonstandard generation maximal-prefix estimate

The signed-sum input to Rademacher--Menshov is proved from the genuine
bad-scale pieces. The last theorem specializes all geometric hypotheses to
the concrete complete finite shifted-grid tree.

The logarithm here still records the number of finite generations. Removing
that dependence in the source's uniform sparse theorem requires the separate
Carleson overlap pruning; that further conclusion is not asserted here.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers
  KrauseLaceyRademacherMenshov KrauseLaceyThreeShiftGrid

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

                                               
                                                  
                                                                       
                                

                                                                                      
                                                  
                                      
                                                                          
                                            

                                                                      
                                                                             
                                                      
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                                
                                                                         
                                                    
                                                  
            
                                                                           
                                                                      
                                                
                              
                                                                                  
                             
              
                                              
         
              
                                                                                  

                                                                    
                                                                                 
                                                    
                                                                        
                                             
                                                                
                              
                                                                                         
                                                                    

                                                
                                                             
                                                               
                                                                   
                                                                       
                                                            
                                    
                                                        
                                                                                           
                                                                        
                                                                               
                                 
                                                               
                  
         
         
                                                   

                                                
                                                             
                                                               
                                                                     
                                                                                      
                                   

                                                         
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                                
                                                                       
                                                                            
                                                  
                                                                                      
                       
                                      
                            
                                                   
                                                                                              

                                                     
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                                
                                                                             
                                                                                        
                                                               
                                                                                       
                                                                    
                                                                 
                                                                                                

                                                                   
                                                                       
                                                                
                                                          
                                                                            
                                                                   
                                                         
                                                    
                                                                             
                                                                                        
                                                               
            
                                                                        
                                                                    
                                                                             
                                                                        


end KrauseLaceyBadScale
end QuadraticCarleson
