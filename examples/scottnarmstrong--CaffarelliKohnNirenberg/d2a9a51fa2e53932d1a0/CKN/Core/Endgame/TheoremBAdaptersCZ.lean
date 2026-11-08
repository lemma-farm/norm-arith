-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.IdentificationCZP1Unconditional

/-! # The `ext:CZ` pressure interface of `thm:B`

The Calderón--Zygmund display `ext:CZ` for the centred first pressure
potential enters the theta-decay display of `thm:B` as an almost-every-time
time-slice certificate: membership of `pressureP1` in `L^{3/2}` on the space
slice together with a ball-local `lpNorm` bound in terms of `utensorNorm`.
The slice transfer `pressureP1_thetaDecay_hCZ_of_global_slice` converts one
such certificate into the `r`-scaled extended-real estimate on the
concentric parabolic sub-cylinder.

This module re-quantifies that transfer over all suitable weak solutions at
a fixed integrability exponent, so a single named hypothesis supplies the
exact pressure binder consumed by the gradient criterion of `thm:B`.  The
constant relation is the one exposed by the transfer: the cylinder constant
`C₁₂_p1` dominates `C_CZ * (9 * sobolevPoincareL6Constant)`. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3

set_option autoImplicit false

noncomputable section

namespace CKN

namespace Core.Endgame

                                                                             
                                                                            
                                                                     
                                                                           
                                                                      
                                                                           
                                                                          
                                      
                                       
                                          
                                                                     
             
                                  
                                                                        
                                                             
                                                         
                                                      
                                                                  
                                                      
                                           
                                          
                                             
                                                                       
                                                          
                                            
                                          
                                             
                                                                       
                                                          
                  
                                     
                                                                         
                                 
                                                                      
                                                           
                                                       
                                                                          
                                                                
                                         
                                                      
                                        
                                           
                                                                     
                                  
                                                           
                                            
                                             
                                                
                                                 
                                                  
                                      

end Core.Endgame

end CKN
