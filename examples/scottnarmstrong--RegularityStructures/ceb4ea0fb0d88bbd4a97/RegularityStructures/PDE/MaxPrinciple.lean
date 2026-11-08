/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatTime
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Order.Compact

/-!
# A maximum principle on the torus

Let `u : ℝ → C(T³, ℝ)` be a continuous path with `u(0) < L`, which is twice differentiable in
space and differentiable in time on `(0, T]`. If at every point where `u = L` the parabolic
operator is negative, `∂_t u - Δu < 0`, then `u < L` on `[0, T] × T³` (`lt_of_maxPrinciple`).

At the first time `t*` at which `u` reaches `L` the maximum of `u(t*)` is attained at some `x*`,
where `Δu ≤ 0` by the second derivative test in each coordinate direction, and `∂_t u ≥ 0` because
`u(·, x*) < L` before `t*`.
-/

public section

open Set Filter Topology

namespace RegularityStructures.PDE

                                                                                    
                                                                                      
                                                                                 
             
               
                                                    
                                              
                                            
                           
                                                    
                                                     
                                        
                                   
                                     
                     

                                                                                   
                                                                                     
                                                 
                                                   
                                                 
                                                             
                              
                                                       
                      
                                                                             

                                                   
                                                                                               
                                                                                            
                         
                                                               
                                                        
                                                                                    
                                                      

                             
                                                                                
                                                                          
                                             
                                                    
                                                                       
                                                                     
                                                                             
                                       
                
                  
                                                         
                                                                         
                                              
                                                                                
                          
                                                                                     
                                   
                                               
                                                                                            
                  
           
                                      
                                   
                                              
                                                      
                
                 
                   
                                                                                             
                                     
                           
                                     
                      
                                          
             
                                               
                                                  
                                                  
                         
                                              
                                   
           
                                                                    
                                                                                           
                                
                                  
                             
                                                      
                                                      
                                            
                                                       
                       
                                          
                                                                               
                                                                                   
                                                             
                                                                                
                                   
                                                                           
              
                                                                                             
                                                 
                                                                                                       
                  
                                        
                                                    
                                             
              
                 
                                                      
                                                                              
                            
                                       
                                            
                                                                            
                                  
            
                        
                                            
          

end RegularityStructures.PDE

end
