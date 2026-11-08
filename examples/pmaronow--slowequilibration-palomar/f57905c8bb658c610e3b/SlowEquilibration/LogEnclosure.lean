-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SlowEquilibration.Certificate

/-!
# Analytic logarithm enclosure for the nonconvex example

This closes the analytic step of Appendix A, Lemma A.1. Mathlib's derivative
proof of the logarithm expansion gives a thirteen-term lower bound and a
twenty-term upper bound. Exact rational arithmetic proves that these bounds
lie inside the manuscript's stated rational enclosure. The upper bound uses
more terms than the manuscript's sharper thirteen-term tail estimate, with
the same conclusion and no numerical approximation.
-/

@[expose] public section

namespace SlowEquilibration.LogEnclosure

open Finset Certificate

set_option maxHeartbeats 800000

                                                                                
                           
                                          
                                               
                                                                      
                                                          
                                  
                                                              
                                  
                      
                                         
                                                                         
                             
               
                                                                      
                                                             
                                  
                             
                          

                                                              
noncomputable def exampleParameter : ℝ :=
  (45 - 24 * Real.log 6) / (72 * Real.log 6 - 85)

                                                                            
                                                                         
                                

                                                               
                                    
                                                              
                                               
                                      
             
                              
                                   
                              
                                   

                                                                                    
                                                                         
                                                                    

                                                                             
                                                 
                                                                     
                                            
                                                 
                                             
                                                 
                                   
                                                 
                                         
                                                              

end SlowEquilibration.LogEnclosure
