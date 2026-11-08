/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.Polish
                                                             
import MarkovProcess.Continuity.DenseTimeContinuousSupport

/-!
# Kolmogorov support for dense-time trajectory kernels

This file applies the global dyadic-floor modification to the coordinate process of a
dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
dense-time law is supported on restrictions of continuous paths.

No measurability of the totalized modification as a path-valued map, PDE increment estimate,
Markov property of the resulting paths, or Hunt-process assertion is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha]

                                                                                           
                                                                                           
                                                                  
                                                              
                                                                    
                                          
                                                                   
                                          
                                            
                                                                    
         
                                                          
                                                                          
                                                                           
               
                                                             
           
                                                                                      
                                                                
                               

section ContinuousPathKernel

                                                                                              
                                                                                               
                                                    
                                                                             
                                                                    
                                    
                                          
                                                                   
                                          
                                                                                            
                                                               
                                                                             

end ContinuousPathKernel

end Kernel
end
end MarkovProcess
