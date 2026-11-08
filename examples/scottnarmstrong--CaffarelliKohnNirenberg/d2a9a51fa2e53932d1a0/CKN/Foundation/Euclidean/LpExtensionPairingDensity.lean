-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.LpExtension
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.Holder

/-! # Density form of the distributional pairing identity

A continuous dual pairing on `Lᵖ` agrees on a dense set if it agrees there
pointwise.  Here the dense set is that of classes represented by smooth
compactly supported functions, which is the form in which the distributional
identity is checked against test functions in the Caffarelli–Kohn–Nirenberg
argument.  The continuous linear maps `testPairing` implement the pairing
against a fixed dual class and are the device used to pass the identity from
the dense set to every `Lᵖ` input.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

                                                                  
                                 
                                          
                                             
                                        
                                                                            

                                                                          
                                 
                                                                               
                                          
                                                                                         
                                                
     

                                                                             
                                                                            
                                                                             
                                                                     
                                              
                                                                            
                                                   
                                                                                   
                                                                              
                                                                            
                                            
                                                                               
                                                 
                                                      
                                                  
                         
                                                            
                                                               
                              
                           
                                                                
                                                             
                                                      
                                                                      
                                                       
                                       
                               
                                 
           
                                                                    
                                
                                
                                        
                
                                    
                                      
                                                    
                                    
                                                
                                                                 
                                                
                                                                    
                        
                       
                                                                                  
                                                                
                              
                               
                                                             
                   
                                                    
                                        
                              
                               
                                                          
                   
                        
                              
                         
                                                                  
                                                                         
                                              
                                                         
                                                      
                                                
      
                                                      
                                                                           
                             
                                     
             
                                                                     
                            
                             
                                                 
             
                                                 
                                                   
                            
                             
                                                
             
                              
                             
                                              
             

end CKN.Foundation.Euclidean
