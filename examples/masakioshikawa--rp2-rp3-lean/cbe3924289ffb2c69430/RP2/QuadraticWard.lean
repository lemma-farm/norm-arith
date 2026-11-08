module

public import RP2.QuadraticDerivatives
public import Mathlib
public section

/-!
# Second and fourth Ward identities for the quadratic interaction

The change-of-variables and fourth-derivative proof pattern is adapted from
OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
All energy derivatives refer to the squared interaction in QuadraticGibbs.
-/
namespace RP2.Quadratic
noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

                                                                          
                                                       
                                              
                                                               
                                                         
                             
                                                                 
                                                                             
                                                                                         
            
                                     
                
                                         
                                                                   
                                             
                    
                                         
                
                                                                      
                                                                                 
            
                                                            
                                                                       
                                                        
                                                                                                    
                                                             
                                                                           
                              

                                                                         
                                 
                                                   
                                                            

                   
                                                                                      
                                                        
                                                                             

                   
                                  
                                                                            
                                        
                                                                                
                                                              
                                                                                   

                   
                                                                         
                        
                                                     
                               
                                         
                                                                              
                                                                           
                                                                           
             
                                                                                  
             
                                                               
                                             
                              
             
                                                             
                                                                                             
               
        

                                                         
                                                                           
                                              
                                                                                  
                                               
                                                   
                                                                                
                          
                                                                   
                                                                            
                                                                         
            
                                                          
                  
                    
                                                      
                                                     
                                                  
                                                                       
                                                      
                                                  
                                                                       
                                           
              
                                                 
                                                                
                                                  
             
                                                        
                                     
                 
                                                                                                                
                                                                          
                                                               
                                                                          
                                                               
                    
                                                                           
         
                                      
                                         


end SpinSystem
end
end RP2.Quadratic
