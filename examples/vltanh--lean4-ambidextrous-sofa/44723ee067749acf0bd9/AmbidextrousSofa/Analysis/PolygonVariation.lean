module

public import AmbidextrousSofa.Analysis.FiniteVariation

@[expose] public section

/-!
# Actual finite polygon support variations

`upperPolygon` is a bounded intersection of the unit strip, two actual
horizontal endpoint walls, and finitely many upper supporting halfplanes.
The outward variation changes one halfplane parameter. Every unchanged
support remains exact, while a strict point in the moved face gives an
attaining point for the increased support. Such a strict point is derived
from any two distinct points of the face when the other normals are
nonparallel; it is not a separate variational assumption.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

                                                                                 
                                                                               
                                                                          

                                                                                          
                                        
                                                                                       
                                                                                         

                                                                                
                                                 
                                                
                                                                                                    

                                                                                  
                                                   
                                                                             
                                                        
                                                     
                                                                         
                                                                                  
                                                                               
                                                                                      
                                                                    
                                                                                 
                                                                                       

                                                                                         
                                                                             
                                                                         
                                                                                   
                                                     
                       
                                                 

                                                                          
                                                                            
                                                                  
                                                                       
                                                     
                                              
                                                             
                                                  
                                 
                                                                                            
                                                                   
                                                                        
                                                              
                                            
                                                                       
                                                                                
                                                                                   
                                                                           
                                                                               
                                                               
                                                                                      
                                
                                        
                                                                           
                                                                     
                                            
                                                                            
                                    
                                     
                                  
                            

                                                                        
                                   
                                                                           
                                         
                                                                          
              
                                 
                                                                                                  
                                                                                          

                                                                            
                                                                        
                                                                            
                         
                                                                                       
                                                             
                                               
                                                     
                        
                                                                      
                                                     
                                                             
                                                                          
                  
                                                                                
                                                                               
                                                                               
                                                                           
                                                                            
                                                                        
                                                                                              
                                        
                                                                
                                                                                       
                              
                                                                                       
                              
                                                                    

                                                                       
                                                                    
                                                                            
                                                                    
                                                           
                                                   
                                                                           
                                                                                  
                                                           
                                                           
                                                                                           
                                                     
                        
                                                                    
                                                  
                                 
                                                                                         
                                                                                                
                 
                                                                                                   
                                                       
                                                                                                    
                                                                                           
                                
                                     
                                                                
                                                      
                                                                   
                                                                                        
                                                                                               
                                               
                                                                    
                                                                      
                                    
                                                                                                  
                                
                                                                      
                                 
                 
                                                   
                                                                 
                                                                                     

end FinitePolygon

end AmbidextrousSofa
