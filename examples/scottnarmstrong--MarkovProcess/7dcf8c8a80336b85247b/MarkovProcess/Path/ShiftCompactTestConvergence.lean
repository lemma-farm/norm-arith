/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.AllTimeFiniteMarginals

/-!
# Dominated convergence for shifted continuous-path tests

This file records path-side dominated-convergence tools for deterministic times approached by
dense times. The measure is any finite measure on continuous-path space; no Markov or kernel
assumption is used.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

                                                                               
                                
                                                                                       
                                                      
                                                       
                                                              
                                    
                                                                              
                                               
                            
           
                                                                           
                                                   
                                                
                            
                                                                   
                                                                 
                                                                         
                                                       
                                
                                      
                                                     

                                                                               
                                
                                                                                             
                                                                              
                                                                   
                                                              
                                    
                                                                              
                                                    
           
                                      
                                                   
                                               
           
                                    
                                                               
                              
                                                               
                                                
                            
                                                                        
                                                       
                                                              
                                                         
                                
                                                                                    
                                                        
                                                              
                                        
                                
                                                
                        
           
                                                    
                                 

end
end MarkovProcess
