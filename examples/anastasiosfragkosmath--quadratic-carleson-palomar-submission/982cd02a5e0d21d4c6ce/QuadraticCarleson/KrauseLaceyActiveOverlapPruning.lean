import QuadraticCarleson.KrauseLaceyActiveCarlesonPacking
import Mathlib
/-!
# Concrete overlap pruning of the actual active family

Intervals entirely inside the high-overlap set are removed. The retained
family has the literal pointwise overlap cap, proved from laminarity. The
exceptional-set estimate below is the proved first-moment bound; no
exponential John--Nirenberg tail is asserted.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

                                                                         
                          
                                                        

                                                                      
                                                           

                                           
                                                        
                                                           
                                                
            
              
                                                                     

                                                                    
                                                                       
                                             
                                           
                                     
                                                          
                                                                                   
                                                                
                                                                 
                   
                         
                 
                                                                
                                             
                                    
                                                           
                                                                         
                        
                            
                                      
                                                                                    
                
             
                                                                         
                           
                                                    
                                                       
              
                               
                                                                           
                                               

                                                                              
                               
                                                               
                                                                 
                                           
                            
            
                        

                                                                
                                                        
                                              
                                                                                            

                                                               
                                                                                
                                              
                                      
                                                        
                               
                                                                                        
                                                    
                                      
               
                                                                     

                                                              
                                                                           
                             
                                       
                                       
                                                               
                                                                                                
                                                                       
                                       
                                
            
                                   
                                                   
                                                         

                                    
                                                                        
                              
                                                          
                                                                                   
                                                                               
                                                                        
                                                                              
                                                                          
                                         
                                                          
                                                                          

                                                                   
                                               
                                                              
                                                                        
                                                        
                                                     
                                          
                                                                        
                                                           
                                                      
                                                                         
                                                   
                                                           
                                               
      
                                                          
               
                                                                                    
                                                                 
                                                                               

                                                                      
                                                                   
                                            
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                              
                                                                                           
                                                            
                                                                                    
                                            
                                                               
                                                                   
                                                              
                                                                                        
                             
                                           
                                                                     
                                                                            
                                                     


end KrauseLaceyBadScale
end QuadraticCarleson
