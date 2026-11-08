module

public import AmbidextrousSofa.Geometry.BarrierAnalysis
public import AmbidextrousSofa.Measure.Partition
                                            

@[expose] public section

/-!
# Actual cap scores and the elementary width branch

The scalar score is now instantiated with the actual cap roof, its actual
horizontal projection endpoints, and the full partial barrier including the
terminal wall. All those functions have the measurability and integrability
properties established in the preceding modules.

This file proves the elementary bound `capScore U α ≤ capWidth U / 2`.
It uses only the cap's height at most one and the barrier's nonnegativity.
Consequently widths strictly below `M` are a strictly suboptimal scalar
branch. No universal bound for larger widths is assumed or claimed.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

                                                                              
                                                              

                                                     
def capWidth (U : Set Plane) : ℝ := horizontalRight U - horizontalLeft U

                                                                       
                              
                                           
                                                           
                                                               
                                        

                                                                                     
                                 
                                            

                                                                                                
                                                                             

                                                                                              
                                                                                        
                                      
                                                                        
                                                                          
                                                                                  
                                 
                                               

                                                                                       
                                                       
                  
                                                          
                                                                                   
                                                                                                    
                                                                 

                                                                             
                                                                                
                                                                                  
                              
                                                          
                                                                                   
                                                                         
                                            
                                                                 

                                                                          
                                                                          
                                                                               
                                                            
                                                                        
                                               
                                                              
                                                                               
                                                                                     
                                                                            
                                                                         
                                                             
                            
                                                                                           
                                                                                 
                                                                                 

                                                                                
                                                                      
                                                                                         
                                        

end AmbidextrousSofa
