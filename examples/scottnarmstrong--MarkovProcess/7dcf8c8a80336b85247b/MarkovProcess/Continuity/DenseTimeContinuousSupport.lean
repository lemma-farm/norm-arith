/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Continuity.DenseTimeContinuousLaw

/-!
# Continuous support from a continuous modification

This file turns a continuous-time modification of the coordinate process of a dense-time law
into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
the simultaneous choice of all dense-time modification identities, which is valid because
`DenseTime` is countable.

The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
-/

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]

                                                                                               
                                                                                             
                                                                                       
                                
                                                              
                                             
                                                            
                                                 
                                                                  
                                               
                                            
         
                                     
                                         
                                                           
                      
                                             
                                    
                                     
                   
          
                       

end Kernel
end
end MarkovProcess
