/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.FiniteMarginals
import MarkovProcess.Restart.MixedPastFuture

/-!
# Finite mixed past/future marginals of continuous trajectories

Every finite collection of rational coordinates drawn from the past through `S` and the shifted
future has the finite transition law on the corresponding union of absolute physical times,
followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
past coordinate and a future coordinate at zero are both retained even though they observe the
same absolute time.

This is a finite-dimensional law identity.  The conditional factorization of that law through
the state at `S` is in `Restart/RationalRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                            
                                                                     
                                                                         
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                                                          
                                               
                                                                     
                                                                          
                                                            
                                               
                                                           
                       
                                                            
                          
           
                                                                        
                     
                                                                 
                                                                             
                
                                                                       
                                          
          
                                                  
                                                                                   
                                                                         
                                                                        
       
                           
                                                                 

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
