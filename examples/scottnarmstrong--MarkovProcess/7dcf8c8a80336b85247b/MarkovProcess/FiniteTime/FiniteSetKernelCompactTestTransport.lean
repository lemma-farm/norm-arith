/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
import MarkovProcess.FiniteTime.ProjectiveFamily
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

                                                       
                                                                                         
                                                                    
                                                                         
                      
          
                                                          
                                    
                         
                                                    
                                       
                                                             
                                                               
                                   
                                               
                                     
                                                     
                                                                                          
                       
                                                                    
                                                                              
                   
                                                                                    
                                            

                                                        
                                                                                  
                                                                  
                                                        
                        
                                                                     
                                                                   
                                 
                                                           
                             
                                                                                       
                            
                                                     
                     
                                   
                                                  
                                                               
                      
         
                          
                        
                                                                                  
                                                         
                                     
                                                     
                                                               
                                   

                                                                                                  
                                                  
                                                                  
                                          
                                                                               

                                                                                             
       
                                              
                                                                
                                 
                                                                                 
       
                                                                                         
                              
                                    
                             
     

                                                                                                
                                              
                                                            
                                                                               
                                                            

                                                                          
       
                                          
                                                            
                                                                             
                                                                                   
                                   
                                                                   

                                                                                               
                
                                           
                                                                    
                                                                  
                                               
                                         
                                                 
                                                             
                                                                     
                                                                      
                         
                                                                                 

                                                                                               
                              
                                                                         
                                                                    
                                                                  
                                                            
                                         
                                     
                                                   
                                                      
                                                                                       
                                                                                         

end MarkovProcess.SubMarkovKernelSemigroup
