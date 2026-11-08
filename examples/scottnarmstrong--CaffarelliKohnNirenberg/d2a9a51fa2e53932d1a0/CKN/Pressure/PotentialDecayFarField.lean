-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsBasic
import CKN.Pressure.PotentialDecayGeometry

/-!
# Far-field decay of Newtonian potentials about a general centre

The tail estimates of the Newtonian potential and of its first derivative are stated here for
data supported in a closed ball centred at an arbitrary point `x₀`, rather than at the origin:
on the support of the data a far point `x` with `2 * R ≤ ‖x - x₀‖` satisfies
`‖x - y‖ ≥ ‖x - x₀‖ / 2`, so the Newtonian kernel bounds of `CKN.Foundation.Heat` supply the
same decay with `‖x - x₀‖` in place of `‖x‖`.

These tail estimates are the decay-at-infinity input to the uniqueness half of the
Newtonian representation `ext:newtonian` of the paper, where the difference of two
representations is harmonic on all of space and tends to zero in the `L^{3/2}` average sense.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN

                                             
                                       
                                                  
                                               
                                                      
                                                                           
                                                                                 
                             
                                             
                          
                        
              
                                                          
                                                                    

                                     
                                                         
                                                                     
                            
            
                                                         
                          
                                                           
              

                                                             
                                                                
                         
                                                                        

                                                                                               
                                                                                                
                                                                    
                                  
                                      
                                                              
                                                                         
                                                         
                               
                         
                                                     
                             
               
                               
                          
                                                                            

                                                                                                 
                                                                                             
                                                    
                                                                              
                                                 
                                        
                                      
                                                         
                                             
                       
             
              
                              
                                         
               
                               
                                                             
                                                                   
                                                     
                                                                       
                                                  
                                                 
                                                             
                                                  
        
                                                                   
                                               
                                         
                 
                 
                                                                   
                         
                                                              
                              
                                            
                 
                                             
                                                                     
                                                             

                                                                                               
                                                                                        
                       
                                                              
                                                                              
                                                 
                                                    
                                                  
                                                             
                                                 
                       
             
              
                              
                                                            
               
                               
                                                             
                                                                   
                                                     
                                                                       
                                                     
                                                                       
                                                              
                                               
                                       
                                                                            
                                                  
        
                                                    
                                                 
                                                     
                                         
                 
                 
                                                                   
            
                         
                                                                           
                                                                      
                                                                          

end CKN
