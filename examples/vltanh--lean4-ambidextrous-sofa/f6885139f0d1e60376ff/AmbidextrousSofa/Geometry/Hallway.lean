module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.HullCompact
public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

/-!
# Actual hallway constraints and support tightening

The inner corner is excluded by a disjunction, while both outer walls must
hold. Tightening the two support offsets preserves every original retained
point; it does not assert that the entire convex hull fits the hallway.
The actual outgoing strip is tightened separately and remains a whole-body
condition. These are the pointwise geometric steps GA.1--GA.2 and GA.5.
-/

noncomputable section

namespace AmbidextrousSofa

                                                                

                                                                     
                                  

                                               
                                                          
                                                                                   

                                                                         
                                                       
                                                         
                                                            
                                                                              
                                                                                 
                                                                     
                                         
                                              
                                                                   
                                 
                                                                             
                
                                                       

                                                  
                                                    
                                                    
                                          

                                                                            
                                                              
                                                   

                                                           
                             
                                                               
                                                                               
                                                                         

                                                                                           
                                                   
                                                                    
                                                                 
                                                                            
                                                                                  
                                                                                    
            
                                                                              
                                                                  
                                                                 

                                                                 
                                                                     
                                                            
                                                                       

                                                                            
                              
                                                  
                                                  
                    
                                                                          
                                                                                       

                                                                            
                                                          
                                   
                                                                          
                                                                                
                                                                                             
                                             
       

                                                                                  
                                          
                                                                  
                                                                                                  

                                                                                       
           
                                                                            
                                                                       
                               
                                                                                
                                                            
                                                          
                                                         
                                                                

                                                                                            
                                                                                
                                                               
                                                                             
                                                                 
                                          
                                                                                

                                                                     
                                                                            
                                                                 
                                                                          
                                                                                       
                                                            
                                                                                             
                                          
                          

                                                                     
                                                                               
                                                               
                                                 
                                                
                                                   
                                   
                                                                              

end AmbidextrousSofa
