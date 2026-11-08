module

public import AmbidextrousSofa.Analysis.RoofContinuity
public import AmbidextrousSofa.Geometry.Support

@[expose] public section

/-!
# Hausdorff compactness of the actual cap domain

Nonempty compact subsets of a fixed compact box have Hausdorff-convergent
subsequences. Convexity and downward closure both pass to that limit. Zero
width and zero height are retained, so the compactness statement does not
discard degenerate limits. Support values and projection endpoints converge
as consequences of an explicit distance estimate.

The hyperspace argument follows Mathlib's `NonemptyCompacts` compactness
machinery, also used by `mpc_blaschke` in the moving-sofa source project.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

                                                                     
                                                             

                                                          
                                                                                   
                                    
                                                                                         

                                                                         
                                                                       
                                                      
                                                                                 
                              
                                                      
                                                           
                                                                 
                                                       

                                                 
                                                                     
                                                            
                                                                     
                                                                   
                                                                                          
                                                                                      
                                                                                     

                                          
                                                                     
                                                            
                                          
                                                                                    
               
                                                                                              
                                                                                                
                             

                                                                       
                                                                            
                                                            
                                                   
                                              
                                              
                                                                     
                                                                                           
                                                                                           
                                                              
                                                                                    
                               
                                                                              
                                               
                                                   
                                                
           
                                   
                                  
                                                
                                                            
                                                                                     
                  
                                        
                                                                              
                                                                         
                                                                           
                                                                   
                                       
                                       
                                                        
                                                            
                                                 
                                      
                                                                                                
                             
                                                                                                 
                                                                      

                                                  
                                                                    
                                        
                                                                                           
                                        
                                                                                            
                                                                                    
                                      
                                                       
                                                       
                                        
                                                                                     
                                                        

                                                  
                                                                                 
                 
                                                                                
                                                                  
                                                                        
                                                                                        
                                                                                  

                                                      
                                                                                 
                 
                                                                                  
                                                        
                                       
                                                                                          

                                                                               
                                                             
                                                                                     
                                                                 
                                                                          
                                                                     
                                                                

                                                                                       
                                                             
                                                                         
                                                                                
                                                                                      

                                                                                      
                                                             
                                                                         
                                                                              
                                                               
                                                                    
                                                   

end AmbidextrousSofa
