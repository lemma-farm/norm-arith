module

public import RP2.QuadraticWard
public import Mathlib
public section

/-!
# The noncommuting two-axis identity for RP²

This derives the diagonal fourth-order Ward identity from the *quadratic*
Gibbs weight. In particular, the additional square of the second derivative
in the squared edge interaction is retained.
The response/gauge proof pattern and matrix identity are adapted from
OpenAI's ClassicalON development (Apache-2.0); see NOTICE.
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
