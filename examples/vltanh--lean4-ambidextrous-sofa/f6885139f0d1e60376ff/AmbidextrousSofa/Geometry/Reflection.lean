module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.HullCompact
public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

/-!
# Reflection, physical projection, and the two actual hull caps

Reflection is the actual affine map `(x,y) ↦ (x,1-y)`. Its action on fibers,
supports, and convex hulls is proved directly. Connectedness ensures that the
original body's horizontal projection is already an interval, so convexifying
the body does not enlarge that projection.

The two hull caps are built from the actual hull and its actual reflection.
They retain their common projection, and their reflected intersection recovers
the hull as a literal set. No terminal-angle or sharp-area hypothesis is used.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

                                                                              

       
                                                                                           
                                                          

                                                                                   
                           

                                                                                                
                             

                                   
                                              
                  
                                                          
                                                         

                                                                                               
                                     

                                                                             
                               
                                                                    

                                                              
                                            
                                                          
                                            

                                                                                   
                                                                                
                                  
                                                                   
                                               
                                                                                   
                                                                  

                                                   

                                                                        
                                                                     
                                                                

                                                                             
                                                                              
                                                                                  
                                 
                                                                        
                                                      
                                                                                             
                                                    

                                                              

                                                                       

                                                                                      

                                                                     
                                                                                   
                                              

                                                                         
                                                                                       
                                                                  
                                                       
                                                         
                                                                         

                                                                                
                                                                                 
                                                                                        
                                                                                       
                                              
                                                                                       
                                       

                                                                                     
                                                                                        
                                                                                              

                                                                          
                                                                                    
                                                           
                                                                    
                                                                              
                                                      
                                            

                                                                                   
                                                                             
                              
                                                             
                                                                                      
                                                                                         
                                                           
                                    
                                                            
                                                  
                                                                                    

                                                                                         
                                                                               
                                                                    
                                                                                           

                                                                                       
                                                                    
                                                       
                                                
                                              
                                                                                 
                                                                                    
                                   
                                                                                              

end AmbidextrousSofa
