/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.Basic

/-!
# Finite rational-time marginals of continuous-path trajectories

This file transports the finite-dimensional laws of the canonical dense-time trajectory to
arbitrary finite sets of nonnegative rational times.  The target coordinates are indexed by the
corresponding finite set of physical `NNReal` times, exactly as in `finiteSetKernel`.

No assertion is made at irrational times or about a Markov, strong Markov, or Hunt property of
the continuous-path law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

                                                                                              
                                                                  
                                                

                                                         
                                                
                                 
                                                                                
           
                                            
            
                    
                
                                                                                   
                        
                          
                                       
                
                                                     
                               
                                                  
                         
                                              
                                  
                             
                                                                        
                                                                                 
                                                   
                            
                               
                                                               
                                        
                                                                             
                
                                                       
                                                      

                                                         
                                 
                                                                                   
                   
            
                                             
                                                    
                      
                                                                      
                              
       
                   
                   
                       
                                                  
                                     
      
             
                           
                                                          
                                                      
                               
                               
                                    
                                                      
                 
                                
                                                   
                                                     
                

variable {α : Type*}

                                       
                                                    
                                                                               
                                                             

                                                      
                                                     
                                                            
                               
                                                                      

namespace IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

                                                           
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
             
                                               
                                                                    
                                                                 
                                                                      
                                                         
                                                                      
              
                                                                        
                                                              
                                              
                                                                   
                                                                    
                 
                                             
                                                      
                                        
                                                  
               
                                                                        
                                                      
                                                                 
                 
                                               
                               
                                     
                                                              
                                                            
                                
                                                                   
                                                  
                                                                          
                                                                             
                                                
                                                                        

                                                                                         
                                                         
                                                       
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                            
                                               
                                                          
                                                      
                        
                                                                     
             
                                        
                                                  
                                                     
                                          
                                                               
                                                                    
       
                                  
                                                                      
                                                           
                               
           
                                              
                                                                                         
                                                                  

end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess
