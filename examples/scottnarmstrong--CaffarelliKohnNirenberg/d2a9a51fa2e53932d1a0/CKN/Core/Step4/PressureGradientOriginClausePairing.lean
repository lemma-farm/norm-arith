-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradient
import CKN.Setting.Energy.Calculus
import CKN.Setting.ScalingInvarianceTests

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-! # The origin clause as a full-space pairing

Clause `(OC)` of the paper is stated as an iterated pairing, first in space and
then in time, against a smooth compactly supported test function carried by a
product box `B' ×ˢ J`.  The transfer lemmas downstream consume it instead as a
single integral over the whole space-time carrier.

This file bridges the two shapes.  Because the test function is supported in the
box, the spatial gradient of the test function is supported there as well, so
both integrands vanish outside `B' ×ˢ J`.  Fubini on the product box, applied to
the two integrable products, therefore identifies the box integral with the
iterated one, and the box may be replaced by the whole carrier without changing
either side. -/

                                             

                                           
                                                                           
                                                                               
                                                                                
                                               

                                                                             
                                                                          
                                       
                                                  
                                                          
                                  
                                                               
                                  
                                          
                                          
                                                                          
                                                  
                                                        
                                              
                                                                              
                                  
                                                                                
                                                                        
              
                  
            
                                                                    
                                                                                     
                         
                
                    
              
                                                                      
                               
                           
                                                                                   
                                                                    
                                                                          
                                              
                                                 
                                        
                            
                                                                  
                                                                       
                                                                           
                                              
                                                 
                                        
                                                                  
                                                                  
                                                      
        
                                                         
              
                                                                                        
                                          
        
                                                  
                                     
        
                                                         
              
                                                                              
        
                                                       
                                
                              
             

end CKN.Core.Step4
