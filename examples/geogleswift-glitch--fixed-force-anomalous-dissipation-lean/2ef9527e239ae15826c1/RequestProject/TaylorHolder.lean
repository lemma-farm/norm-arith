module

public import RequestProject.Basic

/-!
# Second-order Taylor expansion with Hölder remainder

For a `C²` function `f` on `ℝ²` whose second partial derivatives are `β`-Hölder with constant
`H`, the second-order Taylor remainder at `z` in direction `δ` is at most `4 H ‖δ‖^{2+β}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                          
                                              
                                                       
                                                   
                     
                                   

                                                                                
                                   
                                                                      
                                                                            
         
                                                   

                                                                                        
                                                                                   
                                                         
                                                            
                                                           
                                     
            

                                                                               

                                                         
                                                                                  
                                                                                          
                                                                                                   
                                   
                                                                  
                                                                   
                                                                                       
                                                                                               
                                             
           
                                                                               
                                                                                                              
                        
                                               
                        
                                    
                                                                                        
                                                                                            
                                                   
                                            
                                   
                                              
                                                        
              
                                                  
                                                           
                                                                              
          
                                                                                       
                               
               
                    
                                     
                                           
                                                                                        
                                                        
                                           
                         
                                                                                                
                                                                      
                                         
                                                                              
                  
                                   
                                                               
                           
                                                                                
                                                        
                                                               
                                                                             
                                 
                      
                                                            
                                                     
           
                                                                                   
                                                              
                                                 
              
                                                                                
                                                                         
                                         
                                                                              
                                                     
                       
                                                                                         
                                              
           
                                                           
                                                    
                                                                                            
                            
                                                                   
                                                                              
                                                                                          
                                       
                                                         
                                                         
                                                                 
                                                                     
                     

end AnomDiss
