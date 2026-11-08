/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.DenseRestrictionMarginals
import MarkovProcess.Feller.DensePhysicalFiniteSetContinuity
import MarkovProcess.Path.Polish

/-!
# Finite dense-time marginals of a restarted trajectory law

Composing the canonical continuous trajectory kernel with a measurable evaluation of the path
and pushing to a finite set of dense times integrates a compactly supported test through the
mapped finite-set kernel at the evaluated state.  The evaluation is arbitrary, so the identity
serves deterministic coordinates and stopping-time evaluations alike.

This is a kernel-level identity of finite-dimensional integrals.  No conditional or
stopping-time statement is proved here; those are in `Trajectory/FellerConditional.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                             
                                                                                               
                                                                                      
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                                                              
                                                          
                                                    
                                                                                     
                                                          
                                                                           
                                                                   
                                                
                                                            
                                         
                                                                            
                                                                     
                                                                           
                                                                                
                
                                                                                  
                                  
                                            
                                                                                        
                 
                                                                                          
                                        
                                                                               
                                                 
                               
                   
                                                                        
                                                                  
                                                                                      
                                                              
                                                                       
                                                                        
                                                
                                       
                                                                     

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
