/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.DenseRestrictionMarginals
import MarkovProcess.Trajectory.RationalConditional
import MarkovProcess.Time.DenseTimeApproximationFromAbove
import MarkovProcess.Path.ShiftCompactTestConvergence
import MarkovProcess.Feller.DensePhysicalFiniteSetContinuity
                                                                      
import MarkovProcess.Path.MeasureIdentification


/-!
# Event-restricted deterministic restart for the Feller trajectory

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the deterministic-time canonical filtration. The proof approaches the
time strictly from above by dense times, identifies every finite dense future marginal by compact
tests, and then uses measure identification on dense restrictions.

The time here is deterministic. The strong Markov property at a finite stopping time is in
`Trajectory/FellerStoppingRestart.lean`.
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
