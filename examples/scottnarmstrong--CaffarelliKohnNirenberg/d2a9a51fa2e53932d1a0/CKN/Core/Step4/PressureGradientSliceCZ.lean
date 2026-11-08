-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientSWS
import CKN.Core.Endgame.ConcreteRieszConsumption
import CKN.Foundation.Euclidean.CZUnconditional

/-! # The slice pressure-gradient bound with the explicit endpoint constant

`pressure_slice_bound_of_riesz_weak_extension` takes the selected
weak-gradient family as a hypothesis.  That hypothesis is now available
without any analytic input: the completed `L^{6/5}` extension of the second
Riesz transforms provides the field, its pairing with the first potential,
and the numerical bound, with the explicit constant
`czGradientOperatorConstant`.  The two statements below record the selected
family at that constant and the resulting slice bound, so the pressure
gradient on a slice is controlled with no Calderón--Zygmund premise.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                                     
                                                                            
                                                     
                                 
                                                                         
                        
                                                     
                                      
                                                       
                                                                                  
                                  
                                                       
                                                     
                                                            
                                                                            
                                     

                                                                        
                                                                           
                                                                  
                                                           
                                
                                          
                                     
                                                 
                                         
                                                      
                               
                                   
                                                   
                                         
                                
                                                          
                                            
                                              
                                                                         
                                                            
                                                                     
                   
                                      
                                     
                                                                   
                                                                           
                                             
                                                                          
                                                          
                                                                                     
                                         

end CKN.Core.Step4
