-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientGluedTwoRegime

/-!
# The every-cell Morrey bound in its two regimes

The every-cell Morrey bound of a field carried by a measurable set has two
regimes.  Below the fixed scale `r₀` the cell of the field is controlled by the
slice growth bound, applied at the cell's own radius.  At or above `r₀` the
cell power integral is bounded by the whole-carrier integral, which is a
constant bound of the growth form at the cost of the explicit scale factor
`r₀ ^ (-(5 (1 - P/κ)))`.  Combining the two gives a single every-cell estimate
whose constant is the sum of the two regime constants, and hence a bound on the
Morrey seminorm itself.

A single uniform argument across all radii does not exist: the slice bound is
available only while the cell is small relative to its distance to the carrier
boundary, so the two regimes must be kept separate and then glued.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                                               
                                                                            
                                                       
                                                     
                                                                              
                             
                                         
                                                   
                                                
                                                                  
                                                               
                                                                        
        
                                                                             
                 
                                                                      
                                                              
               
            
                                                                
                                                          
                                                              
                                                               
                    
      
                                                       
                                                                         
                                                      
                             
                                            

                                                                              
                                                                               
                                                              
                                 
                                                   
                                                          
                             
                                             
                                                         
                                                              
                                     
                                                   
                                               
                          
                                                                           
                                                     
                                                                               
             


                                                                      
            
                                         
                                                                      
                                                                                
                                                                        
                                                                            
                                                                         

                                                                                
                                          
                                                                          
                                  
                                                 
                                         
                                   
                     
                                
                                   
                                      

                                                                           
                                                                         
                                   
                                                           
                                                                          
                                
                                                   
                                                         
                                                 
                                                    
              
                                   
                                                           
                        
                     
                                    
                                      
                                                          
                                                      
                                            
                                             
                                                  
                                             
                                                            
                                
                                                 
                    
                          

end CKN.Core.Step4
