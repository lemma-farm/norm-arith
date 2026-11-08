/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Restart.CountableStoppingRestart
import MarkovProcess.Path.RandomShiftMeasurability

/-!
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

                                                                                         
                                                                    
                                                                              
                                             
                                                     
                                                                 
                                                 
                                           
                                                                      
                                                               
                                          
                                                               
                                                                       
                                                                             
                                                                    
                                                      
                                                                                     
           
            
                                                          
                                                                                           
                                                                            
                         
                                        
                                                                                          
                                          
                                                           
                                                            
                                   
                                                                                    
           
                                  
                                                                              
                                                                                   
                                                                         
                       
                                                                                        
                                                                                        
               
                                                                                
                           
                                                                
             
                     
                                                                      
                                                                      
                                                           
                   
                                                                   
                                                                            
                                                       
                                                    
             
                                                                          
                                                                          
          
                                  
                                                  
                                       
                                                                                        
                                                                       
                 
             
                                                                                            
               
                              
                                                 
                              
                                               
                                                              
                                                     
                                                                         
                                                                       
                                                                                    
                                                                                   
                                  
                                                          
                                                 
           
                              
                                                                          
                                                 
                                                                        
                                                                    
                                                                      
                                    
           
                                                                 
                                                                  
               

end ContinuousPath
end MarkovProcess
