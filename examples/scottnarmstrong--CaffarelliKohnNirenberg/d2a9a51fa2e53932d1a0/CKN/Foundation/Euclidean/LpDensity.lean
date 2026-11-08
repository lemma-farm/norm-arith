-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Density and pairing helpers for Euclidean `Lᵖ`

This file records the approximation facts used when an operator is first
defined on its `L²` carrier and then extended to lower exponents.  The
approximants are continuous and compactly supported; in particular they are
in every finite `Lᵖ` space.  The pairing estimates are stated in the real
integral form supplied by Hölder's inequality, which is convenient when
passing a distributional identity to the limit.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

                                                                          
                                                                           
                                                    
                                          
                             
                       
                                                        
                                                      
                                                                     
                                  
                                                                   
                                                 
            
                    
                                          
                                                                     
                                                   
           
                                                                              
                                                 
            
                    
                    
           
                                                
                                                       
                                                                      
                                                                                  
                                                                               
                               
                                                              
                                                 
                                             

                                                                             
                                                                        
                                                         
                                      
                                              
                       
                                                        
                                                                       
                                                                    
                         
             
                                                 
                                                       

                                                                            
                                                                  
                                                             
                                              
                      
                                  
                                        
                                 
                                  
                                                                 
                                      
                                                                                 
                                                          
                              
      
                                          
                                      
                                
                             
                              
                          
                                                     

                                                                        
                                                                         
                        
                                                                      
                                                               
                                            
                                              
                              
                                          
                                        
                                               

                                                                             
                                                           
                                                          
                                                
                                                                 
                                 
                      
                                  
                                        
                                                                        

                                                                             
                               
                                              
                                                             
                                                                       
                                 
                                                                       
                                                                          

                                                                         
                                          
                             
                                                     
                                    
                                                   
                                      
                                                                     
                                                    
                                                      
                                  
                                                                 
                    
                                
                                        
                                                
                                      
                                                                             
            
            
                                                              

end CKN.Foundation.Euclidean
