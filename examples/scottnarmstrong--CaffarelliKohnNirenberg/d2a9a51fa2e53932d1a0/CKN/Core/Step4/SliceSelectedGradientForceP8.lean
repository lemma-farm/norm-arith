-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.KernelAllOrders
import CKN.Pressure.PkBoundsCylinder
import CKN.Pressure.DecompositionPotentials

/-! # The inner-ball gradient of the second force potential `p₈`

The local pressure decomposition `eq:pk` writes the pressure on a ball as
`p₁ + (p₂ + … + p₆) + (p₇ + p₈)`.  The last summand

  `pressureP8 η f s = fun x => -∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x`

is the second force potential.  With `η = mollifiedBallCutoff x₀ hρ` its density
`spatialDeriv η j · * f (·, s) j` is carried by the cutoff annulus
`pressureAnnulus x₀ ρ = B(x₀, 3ρ/4) \ B(x₀, 13ρ/20)`, so on the inner ball
`B(x₀, ρ/2)` the Newtonian kernel is smooth in the evaluation point and the
potential is `C¹`, with the far-field gradient bound of `eq:har-Ck` and the
separation `3ρ/20` of `lem:cutoff`.  Display (3.5) of the pressure-gradient
section consumes exactly that: the classical gradient of `p₈` on the inner ball,
measured in the Euclidean norm, is controlled by the `L¹` size of the annular
density with a constant that is uniform in the ball and its centre.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                               
               
                                                                                 
                                            
       
                                                                  
                                                                               
                                                  

                                                                              
                                                                               
                                                                       
                                                                                
                                               
                                                     
                                                          
                                                                         
                                                    
                                                                          
                                                    
                                                 
                                                
               
                                                                          
                                                                                 
                                                            
                             
                                                                                     
                                                            

                                                                         
                                                                               
                                                                  
                                                    
                                                                                       
             

                                                                    
                                                                               
                                                                                       
                    

                                                                                
                                                                          
                                                                            
                                                                 
                                                         
                                                                              
                                                              
                                               
                                                     
                                                                                  
                                                                      
                                                                
                            
                                                                                         
                                            
                                                                              
                
                                    

                                                                               
                                                                              
                                                                                
                                         
                                      
                                                                        
                                   
                                                                                 
               
                                                                          
                                 
                                                                              
                            
                                                  
                                                                                    
                         
                                                   
           
                                                                                
                                   
                   
                                                                                     
                  
     

                                                                       
                                                                             
                                                                             
                                                                              
                               
                                                         
                                                    
                                       
                                   
                                                                                 
             
                                   
                                                                       
                                               
                     
                                                                                
                                                             
           
                             
                                                                                
                                                      
           
           
                
                                                         
           
           
              
                                                                                    
                
                  
                                                                                   
               
                                                                              
                                                 
                                                                        
           
                                                                                  
                                             
                           
                                                                       
           
                                                           
                                                
                                                             
                                                                 
                         
           
                                                                              
                                                                     
                                                                                  
                                                                        
                                                        
                                          
            
                         
                                                                        
                                                                              
                           
                                                           
                                                                    
           
                                                                                   
                                                   
                                               
                                                                               
                                                                        
                          
                                               
                                
                                                                 
                                                                          
                                                             
                 
                                                
                                                                                 
              
                 
                                                                          
                                  
                                                                            
                                                                 
                                    
              
        
                            
                                                                                
                                                                   
           
                                
        
                                                                                  
                                                                           
                             
                                             
                                                                              
                                                                                  
                             
                                                                                    
                                                                                
                                                                       
                                                                                            
                                                              
                                                   
                                
                                                                              
                       
                                                                                     
                                                        
                                                                          
                       
      
                                                                                            
                                                                                       
                  
                                                                      
                                                            
                                                                    

end CKN.Core.Step4
