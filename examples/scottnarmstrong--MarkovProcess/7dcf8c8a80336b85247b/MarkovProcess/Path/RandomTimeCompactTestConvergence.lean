/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.ShiftCompactTestConvergence
import MarkovProcess.Kernel.PositiveC0OperatorMeasure
import MarkovProcess.Path.RandomShiftMeasurability

/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

                                                                                                
                                                
                                                                  
                                                              
                                                                                  
                                
                                                                           
                                                                        
                                                              
                                                        
                                                
                            
                              
                                                                                     
                            
                                                                                
                                
                                      
                                                               

                                                  
                                                                                               
                                                                                      
           
                                                                                         
                                                              
                                                                                  
                                
                                                                           
                                                    
                                            
                                                                      
                                    
                                                                        
                                                                                          
                                                                  
                                                                       
                                                       
                                             
                                                                   
                                                
                            
                                
                                                                            
                                                         
                                
                                                                                    
                                                        
                                                                      
                                
                                                
                        
           
                                                    
                                           

end

end MarkovProcess
