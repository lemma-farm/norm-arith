/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.CoordinatePolynomialContinuity
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Continuity of finite-time integrals of compactly supported tests

This file extends finite coordinate-polynomial continuity to arbitrary compactly supported
continuous tests by uniform approximation. Conservativity makes every finite-time law a
probability measure, so the approximation error is uniform in the ordered time family.

The measurable structure on a finite product need not expose an `OpensMeasurableSpace` instance
under the standing assumptions. We therefore derive strong measurability of the test from its
coordinate-polynomial approximants instead of adding that extra assumption. This is
finite-dimensional analytic infrastructure; no statement about path space is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                   
                                                
                                                                        
                                                         
                                            
                                                             
                                                           
                               
                                           
                          
                                                 
                                                                                         
                                                                    
                                                                          
               
                                                                                
                                                                                    
                                                                   
                             
                               
                                                   
                             
          
                                             
                  
                        
                                               
                                                           
                                                          
                
                         
                                                                     
                                
                                                     
                                                      
                        
                                                                    
                                                                                
                                                                 
                               

                                                   
                                               
                                                                                
                                                         
                                                                    
                      
          
                                                          
                                                            
                                                                                   
                                  
                                                      
                         
                                                    
                                                             

                                                   
                                                       
                                                                                  
                                                                         
                      
          
                                                          
                                    
                         
                                                    
                                       
                                                                 
                                                               
                                   
                                               
                                     
                                                     
                                                                                          
                       
                                                                        
                                                                              
                   
                                                                                    
                                            

                                                                                      
                                                         
                                                                    
                        
                                                                           
                                                                   
                                 
                                                           
                             
                                                                                       
                            
                                                     
                     
                                   
                                           
                                                               
                      
         
                          
                        
                                                                                
                                           
                                     
                                                     
                                                               
                                   

                                                                                         
                                                               
                                                                                    
                                                                              
                                                              
                                                                      
                                                               
                                             
                                                                      
                                                                
                          
                        
                           
                                                                           
                                                    
                                                              
                                                                                    
                                                   
                     
                                           
                                                            
                                                                      
                                                          
                                                 
                                                                 
                                      
                                                  
                                                                 
                                                                               
                                                    
                                                               
                                             
                                                         
                               
                      
                                                                              
                                                         
        
                                                                  
                                                                   
                                                       
                                                  
                           
                                                                              
                     
                                                                                
                                         
                                           
                                                             
      
                                                         
                                                       
                                                           
                                                                     
                                                                      
                                                                              
                                                             
                                                                     
                                                                       
                                                                    
                                                                     
                                                                
                            
                               
                     
                                     
                             
                                   
                                       

end MarkovProcess.SubMarkovKernelSemigroup
