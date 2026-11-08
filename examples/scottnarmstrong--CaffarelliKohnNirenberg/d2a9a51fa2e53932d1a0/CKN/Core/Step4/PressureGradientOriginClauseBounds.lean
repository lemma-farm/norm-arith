-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseGeometry
import CKN.Core.Step4.PressureGradientOriginClauseProduct

/-!
# Carrier cell bounds from slicewise bounds on the pressure

The one-sided estimate of `prop:bootstrap` sees the selected pressure gradient
only through the indicator of the backward carrier
`parabolicCylinder 0 0 R₁`.  A cell bound for that indicator is a bound for the
integral of the gradient over the intersection of the cell with the carrier,
and by the product decomposition of that intersection the integral splits into
a time integral of spatial slice integrals whose times all lie in
`(-R₁ ^ 2, 0]`.

This module turns a multiscale slicewise `L^{6/5}` majorant for the weak
gradients of the pressure slices into exactly those carrier cell bounds.  The
majorant is measured on the intersection `vec3Ball x r ∩ vec3Ball 0 R₁` of the
cell ball with the carrier ball, and its two time integrals are taken over the
clipped windows.  Nothing here refers to the gradient at a time outside the
time factor of the unit cylinder.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                           
                                                                           
                                                                       
                                                                       
                                                          
                                                                   
                                                                 
                                                              
                                            
                                                      
                                                     
                                                             
                                                                              
                                                                            
                                                        
                                                             
                                                                              
                                            
                                                                          
                                                                         
                                              
                                                                            
                                                         
                                                           
                                                                                
                      
                                             
                                                                  
                                                    
                       
                                                                  
                                                                             
                                                                 
                                                                             
                                                                 
                                                                       
                                             
                                      
                                                                            
                                     
                                                                        
                                                                         
                                                 
                                             
                                                                                       

                                                                               
                                                                      
                                                                       
                                                                            
                                                                             
                                                             
                                                     
                                                                   
                                     
                                                              
                                               
                                                
                                                               
                                                                                
                                              
                                                                                
                                                                         
                               
                                                         
                                                                
                           
                                                                         
                                
                                                         
                                                      
                                                                  
                                                             
                                                                              
                                                                              
                                                               
                               
                                                                               
                                                                              
                                                             
                                                       
             
                          
                                                                                 
                                                              
                                
           
                                                                                       
                                                
                                                               
                           
                                                                                      
                               
                     
                                

end CKN.Core.Step4
