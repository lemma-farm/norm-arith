-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SliceSelectedGradientTensorSource
import CKN.Core.Step4.SliceSelectedGradientTensorSourcePairing
import CKN.Foundation.Parabolic.Vec3Norm
import CKN.Pressure.SliceVelocityCube
import CKN.Foundation.Measure.SliceDistribution

/-!
# The local tensor source of the pressure gradient

The source and its tested pairing in `eq:pressure-gradient-morrey` follow
from the velocity's spatial weak gradient and divergence constraint.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                                        
                                                                    
                                           
                                      
                                                                    
                                                        
                                                            
                                             
                                                                     
                    
                                                  
                                   
                                                   
                                                                                  
                                                             
                                              
                                               
                                                   
                                                                                  
                                                                
                                                                    
                                                              
                                                                                  
                                                                                    
                             
                                                                                               
                                                                         
                                                     
                                                         
                                              
                                                           
                                                       
                                                                         
                        
                                                   
                                                              
                                     
                                                           
                                                     
                                                                      
                      
                                                            
                                                                               
                                   
                                                                 
                
                                                
          
                                                       
                                               
                                                       
                                                       
             
                                                                  
                                                        
                                                                    
                                              
                                                          
                                                        
                                                                               
                                                         
                                                                     
                                                                                   
                                                                    
                                                
                                              
                                            
                                                                               
                                                
                                           
                                                              
                                                               
                                                                  
                                       
                                                          
                                                                                         
                                                         
                      
                
                                                                                    
                                                                              
                

end CKN.Core.Step4
