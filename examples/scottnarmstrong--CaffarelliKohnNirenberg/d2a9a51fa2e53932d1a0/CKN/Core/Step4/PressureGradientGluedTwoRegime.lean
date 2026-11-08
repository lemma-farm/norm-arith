-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Basic

/-!
# The every-cell growth bound in its two regimes

A cell of the pressure-gradient carrier is controlled by the slice estimate at
its own scale only when its ball still fits inside the carrier at that scale;
a cell that is large relative to its distance to the carrier boundary is not
reached by the slice estimate at all.  The growth bound `A · r ^ (5 (1 - P/κ))`
of the parabolic Morrey class therefore has two regimes.

Below a fixed scale `r₀` the bound is the slice bound at the cell's own radius.
At or above `r₀` the cell power integral is bounded by the whole-carrier
integral, and because the growth exponent `5 (1 - P/κ)` is nonnegative for
`P ≤ κ`, that constant bound is itself of the required form, at the cost of the
explicit scale factor `r₀ ^ (-(5 (1 - P/κ)))`.

The two regimes are combined here into a single every-cell statement whose
constant is the sum of the two.  Attempting one uniform argument across all
radii is what makes a growth clause unsatisfiable.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                                            
                                             
                                                  
                                                   
                                                          
                                                       
                                                                             
           
                                                          
                                                      
                                                                          
                                                         
                                   
                                               
                                
                        
                                   
                                                  
                                        
                                   
                

                                                                              
                                                                           
                
                                                  
                                                    
                                             
                                              
                                              
                                   
                                                        
                                                    
                                          
                                  
                                                                       
                                                                      
                                                          
                                                       
                                                                     
                                                                    
        
                                                                     
                                                   
                                 
                                                        
                                               
                                                                     
                    
                                                             
                                                        
                                                          
                                                           

                                                                           
                                                                             
                                              
                                                
                                                   
                                                          
                             
                                             
                                                         
                                                              
                                     
                                                     
                                           
                                     
                                                              
                                                      
                 
                                     
                                          
          
                     
                                                                     
                                                                        
                          
          
                     

end CKN.Core.Step4
