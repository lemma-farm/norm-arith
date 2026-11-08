module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
                                                        
                                                             
                                                                 

@[expose] public section

/-! # Actual local energies of coordinate gradients

Localization acts on L2 gradients, not on Sobolev functions: multiplying a
function by an indicator would introduce a distributional boundary term.
The local energy below is exactly the coefficient-weighted set integral.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                       
                                                                   
                                                                             
                                  
                                          

                                                                                   
                                                                                    
                                                         
                                                                               

                                                                          
                                                                                                    
                                                    
                                             
                                                                                             
                                                                                         

                                   
                                                                                               
                                                                                      
                                                                                                                  

                                                           
                                                                                           
                                                    
                                                                     
                                                                  
                                                            
                                                                        
                                       

                                                                            
                                                                         
                                                                                         
                                                                                                       
                                             
                                                                            
                                                                               

                                                                         
                                                                        
                                                                                         
                                                                                     
                                                                     
                                                 
                                                                               

                                                                        
                                                                                               
                                                      
                                                                 
                                                
                                                                           
                                    
                                                                                         

                                                                                 
                                                                                 
                                                                                  
                                                                                                     
                                                                                               
                               
                                                                       
                                                                                                 
                                             
                                                                                 
                                                                       
                                             
                                                                                            
                                                   

                                                                           
                                                                                   
                                                                   
                                                                                                     
                                                                                               
                             
                                                                       
                                          
                                             
                                                                                 
                                             
                                             
                                                                                                       

end SubdiffusiveProcess
