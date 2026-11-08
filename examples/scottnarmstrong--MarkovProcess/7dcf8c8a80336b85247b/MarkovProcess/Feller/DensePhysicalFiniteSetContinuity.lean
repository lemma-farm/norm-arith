/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.DenseTime.PhysicalCompactTestTransport
import MarkovProcess.Feller.FiniteSetCompactTestContinuity
import MarkovProcess.Kernel.PositiveC0OperatorMeasure

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Continuity

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                                                         
         
                                                                                           
                                                                              
                                                                            
                                 
                                                      
                                                     
                                                                             
                                                                               
                                                                                           

end Continuity

section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

                                                                                          
                              
                                                                               
                                                                
                                                                
                                                               
                                                  
                                                                         
                                                           
                                         
                              
                                                                        
                                                                  
                                                                                      
                                                                           
                              
                                                               
                               
      
                                                   
                                                     
                               
                         
                                                                                   
                                        
                  
                                                                            

end Bound

end MarkovProcess.SubMarkovKernelSemigroup
