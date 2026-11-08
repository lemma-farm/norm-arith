/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.FiniteDenseApproximationContinuity

/-!
# Arbitrary-time finite marginals of Feller trajectories

This file removes the compact-test convergence premise from the earlier arbitrary-time
finite-marginal reduction. For a conservative Feller kernel semigroup whose dense trajectory has
the stated Kolmogorov control, every finite family of continuous-path coordinates has exactly the
finite-set-kernel law.

The theorem is stated for an arbitrary such semigroup; no particular semigroup is singled out,
and no Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

namespace SubMarkovKernelSemigroup

open IsConservative

variable [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                            
                                                                        
                                                                          
                                                                              
                                                            
                                          
                                                 
                                                         
                                                               
                                        
                         
                                               
                                                                      
                               
                                                         
                                                                                     
                          
           
                                                                                  
               

end SubMarkovKernelSemigroup

end

end MarkovProcess
