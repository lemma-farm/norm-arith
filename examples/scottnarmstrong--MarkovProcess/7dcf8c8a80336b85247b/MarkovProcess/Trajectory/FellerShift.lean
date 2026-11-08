/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.KernelIdentification
import MarkovProcess.Trajectory.DenseRestrictionMarginals
import MarkovProcess.Trajectory.FellerFiniteMarginals
import MarkovProcess.FiniteTime.FiniteSetKernelShift
                                                           

/-!
# Deterministic shifts of Feller trajectory laws

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
every deterministic nonnegative time. The proof identifies all finite coordinates of the dense
restriction and then uses injectivity of dense restriction on continuous-path kernels.

This is an unconditional kernel-law identity. The conditional form is in
`Trajectory/FellerConditional.lean` and the strong Markov property in
`Trajectory/FellerStoppingRestart.lean`; no Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                              
                                                                   
                                                                  
                                                                              
                                                            
                                          
                                                 
                                                         
                                                               
                                        
                  
                                                                          
                                                              
                                                
                                             
                                             
         
                                 
                                 
                                                                         
                                                                            
                                                                     
                         
                                                                                  
                                               
                                                         
                                                                               
                                                                                   
                     
                                                                      
                                                    
                                                               
                                                            
                                                        
                                              
                  
                                                       
                                         
                                                       
                                      
                                         
      
                                                                               
                       
                           
                                                                           
                                                                                    
                                                                 
                              
                                                     
                                           
                                                                             
                       
                                                
                                          
                                                 
                                                         
                                                                    
                                    
                                                                       
                               
                                                                        
                                                     
                                                                               
                                              
                                                     
                                                          
                                  
                                                                 
                          
                                                                                   
                                                                                   
                          
                                                                                   
                                           

end
end SubMarkovKernelSemigroup
end MarkovProcess
