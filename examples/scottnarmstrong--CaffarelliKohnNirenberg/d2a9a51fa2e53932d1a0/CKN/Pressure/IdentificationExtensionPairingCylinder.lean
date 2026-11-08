-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.IdentificationExtensionPairing
import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Pressure.PkBoundsCylinder
import CKN.Foundation.Parabolic.Integration.Average

/-!
# The identification data on a parabolic cylinder

The identification data for the leading local pressure, specialized to the
cut-off `mollifiedBallCutoff z.1 hρ` of the parabolic cylinder of radius `ρ`
about `z` and to the ball average of the velocity used as the subtracted
constant.  The conclusion is stated on the cylinder's time interval, which is
the form the slice pressure estimates consume.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

set_option autoImplicit false
noncomputable section

namespace CKN

                                                                               
                                                                            
                                                                             
                                                                               
                                             
                                                            
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                  
                                                                    
                                                                        
                                             
                                                                              
                                                    
                                                        
                                               
                                                                                
                                              
                                 
                                                          
                                                                   
                                                    
                                                                
                                                                     
                                                                        
                                             
                                                                              
                                                        
                                                                          
                                     
              
                                                
                                                         
                                                          
                                         
                                                     
                                                
                                                     
                                         
                                                        
                                       
                                                                         

end CKN

end
