/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.FellerRestrictedRestart
import MarkovProcess.Restart.CountableStoppingRestartMeasure
import MarkovProcess.Path.RandomTimeCompactTestConvergence
import MarkovProcess.Path.DenseRestrictionIntegral
import MarkovProcess.Trajectory.DenseRestrictionIntegral
                                                   

/-!
# Event-restricted restart of the Feller trajectory at finite stopping times

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the stopped sigma-algebra of any finite `NNReal`-valued stopping time
for the canonical filtration.  The proof approximates the stopping time from above by its dyadic
ceilings, which have countable range, applies the all-time deterministic restart identity on
their level sets, identifies every finite dense future marginal by compact tests and dominated
convergence, and concludes by measure identification on dense restrictions.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                          
                                                                                           
                                       
                                                                                        
                                                                              
                                                            
                                          
                                                 
                                                         
                                                               
                                        
                                                   
                                                                              
                                                 
                                                                           
                                                                  
                                                              
                                                            
                                         
                                                                       
                                                                        
            
                                                        
                                     
                                                                                                
                                                                                          
                                                               
                                             
                                          
                                                                     
                                                                          
                                                      
                                                                              
                                                                                  
                                                     
                                                                                          
                                                                                         
                                                                     
                                                                                         
                
                                                            
                                                            
         
                                                        
         
                                     
                                                    
                                                   
                                                    
                                
                                                                              
                                                                                
                                           
                                                                     
                                                                              
                                               
                                                                           
                                              
                                                                                                 
                             
                                                                     
                                                                
                                                                  
                                                                       
                                          
                                                                   
                                               
           
                                                                   
                                                                         
                                                                          
                                                                  
                                                                                    
                              
                    
                                                                                     
                                       
                                                                                          
               
                
                                                                                       
                                           
                                                                
                                                                
                                                                                  
                      
                  
                                                                    
                               
                                                                                        
                  

end
end MarkovProcess.SubMarkovKernelSemigroup
