/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.FellerRestrictedRestart

/-!
# Deterministic-time conditional expectation for the Feller trajectory

At every physical time, the conditional expectation of a bounded strongly measurable functional
of the shifted canonical Feller trajectory, given the canonical filtration at that time, is the
path-kernel expectation started from the current state.  The proof passes the event-restricted
deterministic restart identity through the generic continuous-path conditional-expectation
bridge.

The time here is deterministic.  The corresponding statement at a finite stopping time is in
`Trajectory/FellerStoppingConditional.lean`, and at a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

                                                                                              
                                                                                                
                 
                                                                      
                                                                              
                                                            
                                          
                                                 
                                                         
                                                               
                                        
                            
                                                              
                                        
                                                           
                                         
                                                                
                                                  
                                                                       
                       
                                                                              
                                               
                                                             
                         
            
             

end
end MarkovProcess.SubMarkovKernelSemigroup
