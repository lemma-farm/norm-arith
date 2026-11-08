/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.CoordinateProductActiveReduction
import MarkovProcess.Feller.BackwardC0Integral
import MarkovProcess.FiniteTime.KernelRestriction

/-!
# Continuity of finite-time integrals of coordinate-product terms

This file proves continuity, under coordinatewise convergence of ordered times, of the
finite-time-kernel integral of one `PiContinuousMap.CoordinateProductTerm`.  The proof reduces
to the coordinates on which the term has factors and applies the backward `C₀` recursion.

When there are no active coordinates, the integrand is its scalar coefficient.  That branch
uses conservativity to identify the finite-time law as a probability measure; in particular,
it never attempts to construct a constant-one element of `C₀`.  This is finite-dimensional
analytic infrastructure; no statement about path space is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                                                        
                                               
                                                                                       
                                                                              
                                                              
                                                                      
                                                               
                                                                              
                                                                                         
                                                                                   
                                                         
                          
                                                                           
                                     
                                       
                                                          
                                                                             
                                                                                 
                                                                                          
                                               
                                                                                          
                                                            
                                                   
                                                
                                                         
                       
                            
                                                      
                                                              
                                    
                                                         
                                                       
                                                                              
                                                                  
                                           
             
                     
                                               
                                                                   
                                               
                                           
                                          
                                          
                                          
                                                                      
                                                                                  
                                           
                                     
                                                                                
                  
                                                                               
                                                                             
                                                          
                                                      
                                        
               
                                                           
                                                                        
                                                                               
          
                                                                   
                                      
                                                                                       
                                     
                                      
                                      
                                                                                       
                                     
                                               
                                                                                     
                                                                                     
                              
                                                                            
                                        
                                               
                                                        
                                                              
                                                                                 
                                                                        
                       
                                
                                                        
                                                         
                                                                                     
                        
                                            
end MarkovProcess.SubMarkovKernelSemigroup
