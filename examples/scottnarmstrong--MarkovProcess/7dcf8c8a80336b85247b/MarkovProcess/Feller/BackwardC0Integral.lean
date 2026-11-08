/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.BackwardC0Recursion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-time integral represented by the backward `C₀` recursion

The backward Feller-semigroup recursion for a nonempty ordered family of `C₀` factors evaluates
to the integral of their coordinate product against the corresponding finite-time kernel.  The
proof follows the recursive kernel construction and uses composition-product integration.

No conservativity assumption is needed: sub-Markov finite-time kernels already give finite
measures, which suffice for bounded integrability.  This is an analytic identification only; no
statement about path space is proved here, and the process itself is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                   
                                            
                                                   
                                                                   
                                                                         
                                                                   
                                                     
         
                                                             
                                  
                                                                                      
                                
                  
                                                       
             
                                                                   
                                                       

                                                                            
                    
                                               
                                                
                                                                                    
                  
           
                                
                    
                
                                           
                                                      
                                                                     
                             
                                                               
                    

                                                                                            
                      
                                                                             
                                                                         
                                                
                                                        
                                   
                                                                       
                                 
           
                                                         
                                                  
                           
                                                     
                                                           
                                                                       
             
                 
                            
                
                                           
                                                      
                                                                     
                                                            
                                                    
                                          
                                                              
                                                                      
                                                                                  
                                                         
                                                               
                           
                                      
                                             
                                                 
                                                    
                                       
                                                
                                                      
                                          
                              
                                                                 
                                                         
                                              
                                                          
                                                         
               
                
                                     
                    
                             
                              
                                                                                    
                                                 
                        
                                                                      
                                                                     
                
                               
           
                                    
                                                   

end MarkovProcess.SubMarkovKernelSemigroup
