-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.HarmonicPartBoundsAE

/-! # Interior regularity of the harmonic pressure part on a slice

The harmonic summand `p₂ + p₃ + p₄ + p₅ + p₆` of the local pressure
decomposition `eq:pk` is a Newtonian potential whose density is carried by the
cutoff annulus `B_{3ρ/4}(x₀) \ B_{13ρ/20}(x₀)`.  On the inner ball
`B_{ρ/2}(x₀)` the kernel is therefore smooth in the evaluation point, and the
potential inherits every finite order of differentiability (`eq:har-Ck`).

This file records the order-one consequence in the almost-every-time form that
display (3.5) of the pressure-gradient section consumes: for a suitable weak
solution and almost every time of the one-sided interval `J_ρ`, the harmonic
pressure part is `C¹` on `B_{ρ/2}(x₀)`, so its weak gradient there is its
classical gradient.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                                     
                                            
       
                                                                  
                                                                               
                                                  

                                                                            
                                                 
                                                
                                                             
                                                   
                                                       
                                                       
                                                       
                                                     
                                                       
                                                                  
                                                                                    
                                                                     
                                            

                                                                       
                                                                         
                                                  
                                                
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                  
                           
                                                            
                                                                
                                              
                                         
           
                                                  
                                      
                                
                                                                                   
                                                                          
                                                            
                                     
                                                                             
                                                     
                                                                   
                                                        
                                                 
                     
                                                                          
                                                        
                                                            
                                              
                                           
                                                              
                                                       
                                                                                
                                                     
                                           
                                                             
                                                                      
               
                                                  
                                                                  
                            
                                                      
                                                                               
                                            
                                                                             
                                                                              
                                                          
                    
                         
                                                                            
                                         
                                                                             
           
                                                    
                                                 
                                                                           
                                                                            
                                                          
                                                                      
                             
           
                                             
                             
           
                                             
                                                                       
                     
                                                                
                                                      
                                                   
                             
                                                                
                                               
                                                                
                                                                     
                                                                 
              
                                                                             
                                                          
                                                                              
                                                          
                                                    
                                                   
                 
                                                                            
                                                                                   
                                                               
                               
                                                                          
                    
                                                               
                             
                                
                                                 
                                                                          
                                                                         
                                                     
                                                                              
             
                                                                
                         
                           
                             
                               
                                 

end CKN.Core.Step4
