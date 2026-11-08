/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.CoordinateProductContinuity

/-!
# Continuity of finite coordinate polynomials

Continuity of finite-time integrals for one coordinate-product term extends to every finite sum
of such terms.  The proof supplies explicit bounded integrability for the individual terms and
their coordinate polynomials before applying linearity of the integral.

This file handles only explicit finite coordinate polynomials.  The passage to arbitrary
compactly supported continuous tests is in `Feller/FiniteTimeCompactTestContinuity.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                   
                                                
                                                                        
                                                         
                                            
                                                             
                                                           
                               
                                           
                          
                                                 
                                                                                         
                                                                       
                                                                             
               
                                                                               
           
                                                                                    
                                                                   
                             
                               
                                                   
                             
          
                                             
                  
                        
                                               
                                                           
                                                          
                
                         
                                                                     
                                
                                                     
                                                      
                        
                                                                    
                                                                                
                                                                 
                               

                                                   
                                               
                                                                                
                                                         
                                                                    
                      
          
                                                          
                                                            
                                                                                   
                                  
                                                      
                         
                                                    
                                                             

                                                                                      
                                                               
                                                                                      
                                                                              
                                                              
                                                                      
                                                               
                                                                                      
                                                                            
                                          
                                                                    
                                            
                      
          
                                                                                    
                      
                              
                         
                                                 
                                                                           
                                       
                                                                         
                                                                     
                                             
                                                              
                                                     
                                                      
                          
                                                       
                                                       
                         
                                                                            
                            

end MarkovProcess.SubMarkovKernelSemigroup
