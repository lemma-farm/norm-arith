/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.Basic
import MarkovProcess.Kernel.C0SemigroupJoint
import MarkovProcess.Feller.Semigroup
import MarkovProcess.Kernel.PositiveC0OperatorMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Order.IsLUB

/-!
# All-time marginals of continuous-path trajectories

This file supplies the rational-approximation input for extending the already proved dense-time
marginals to arbitrary nonnegative real times.  The extension uses path continuity on one side
and Feller `C₀`-orbit continuity on the other.

No continuous-time Markov, strong Markov, or Hunt-process assertion is made here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

                                                                                             
                                                   
                        
                                                                               
                                                                      
                                    
                                           
                                                          

namespace SubMarkovKernelSemigroup
namespace IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                               
                               
                                                
                                                                
                                                                     
                                          
                                                 
                                                         
                                                               
                                        
                  
                                                                               
                                                  
                                                   
                  
         
                                                        
         
                                                
                          
                                                               
                      
                                                                            
                                                    
                                                  
                              
                              
                                                        
                                                                     
                                                           
                                  
                                                                                      
                                                          
                                                    
                                  
                                                         
                                                              
                           
                                                                           
                                                   
                        
                                                                                
                                       
                  
                                                                             
                                                                
                                                                                    
                 
                                                                      
                                                                         
           
                                                          
                                                               
                                                                  
                            
                                                                      
                                                                         
                                                                 
                                                
                                                      
                                                                   
                                                    
               
                                                                              
                                                                                 
                                
                                 
              
                              
                                             
              
                                                                              
                                                                              
              
                     
                                                     
                                                        
                            
                                                                     
                                                                             
                                                
                                                                                      
                              
                         
                
                            
                                           

end IsConservative
end SubMarkovKernelSemigroup

end
end MarkovProcess
