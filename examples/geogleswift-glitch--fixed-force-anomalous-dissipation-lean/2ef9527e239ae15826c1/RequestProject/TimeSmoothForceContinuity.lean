module

public import RequestProject.Basic

/-!
# Joint continuity of time-smooth Hölder-valued forces

The derivative in the specified Hölder norm implies a local uniform time
bound. Together with continuous spatial slices this proves genuine joint
continuity, and hence supplies the forcing input for the finite ODE systems.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                         
                                                               
                              
                                                           

                         
                                                        
                                                                                
                                                                        
                                                             

                                                                           
                                                                 
                                                               
                                                                
                                       
                                                
                                     
                                                
                                             
                                 
                                                               
                                                                       
                                 
                                                
                                                          
                                                                                  
           
                                                                     
                                                                                  
                               
                                                                              
                                                                      
                                                      
                                                                             
                                                           
                                                                                                        
                    
        
                                                                       
                                                     
                                                                                    
                                                                  
                    
                                                            
                      
           
                                                                              
                                                                         

                                                                         
                                                                               
                                                                          
                                                                  
                                                    
                                       
               
                                                      
                                                      
                                                                            
                                                         
                                         
                                                 
                                         
                                                  
                                                   
           
                                             
                               
                                                                                 
                                                                
                                                               
                            
                                              
                                                                        
                                                                       
                                     
                                
      
                                                                           
             
          
                                                                    
                                                                       

                                                                         
                                                                          
                                 
                                  

                                                                       
                                                                     
                                                         
                                                                                       
                                                             
                                                                                    

                                                                           
                                                                                     
                                  

                                                                        
                                                                  
                                  
                                       
         
                                                       
                                                      
                                                              
                                                                                      
                                               
                                                                               
                                                   
                                                                                
           
                              
                                         
                               
                                                                         
                                                                     

                                                                  
                                                                              
                                                                           
                                             

end AnomDiss
