module

public import AmbidextrousSofa.Analysis.EndpointPressure
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

/-!
# Simultaneous wall and endpoint variations

The finite wall integral is differentiated while both integration endpoints
move. A uniform wall-velocity bound controls each moving sliver by a
quadratic error. This accounts for all endpoint terms without differentiating
an indicator or assuming that the end faces have positive height.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

                                                              
                                                              
                                                                                             
                                                                          

namespace WallExpr

variable {ι : Type*}

                                                                       
                                                                              
                                                             
                                                                
                     
                                                           
                                 
                                               
                                                                                  
                                                                           
                                                 
                                                                                                
                                                                      
                                                                        
                                                                                   
                                                                       
                                                          
                                                                                                 
                                                                                         
                          
                                                       
                                                                   
                                                                         
                                                                                              
            
                                                                                          
                                                                                              
                                                                                        
                                                                                       
                                                                
                                                      
          
                                          
                                               
                                                                      
                                           
                                                                      
                                           
        
        

end WallExpr

                                                                         
                                                                   
                                                     
                                         
                                                                             
                                                                             
                                             
                                                                   
                                
                                                                    
                                                                    
                                                                                   
                                                                                   
                                                         
                                                                               
                                                         
                                                                                      
                                                                    
                                                   
                                                             
                                                      
                                                             
                                                                                          
            
                                                                
           
        

end AmbidextrousSofa
