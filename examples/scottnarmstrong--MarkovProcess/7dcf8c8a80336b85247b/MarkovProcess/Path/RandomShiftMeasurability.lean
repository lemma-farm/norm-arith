/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.Shift
import Mathlib.Probability.Process.Stopping

/-!
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

                                                                      
                                                                          
                         
                                                        
                                                                                  
                           
                                                                 

variable [MeasurableSpace alpha] [BorelSpace alpha]

                                                                               
                                                                         
                         
                                                                         
                                                                                  
                           
                                                                                          

                                                                               
                                                                        
                                                               
                                                 
                      
                                     
                                                                
                                                                    

                                                                                           
                                                                         
                                                               
                                                 
                                                     
                                                                      

                                                                                            
                                                                              
                                                               
                                                 
                                                                      
                                                                     

end ContinuousPath
end MarkovProcess
