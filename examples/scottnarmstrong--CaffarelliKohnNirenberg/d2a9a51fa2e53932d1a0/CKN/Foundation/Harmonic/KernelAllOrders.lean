-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.KernelAllOrdersBounds
import CKN.Foundation.Harmonic.KernelAllOrdersPotential
import CKN.Pressure.Potentials
import CKN.Pressure.PkBoundsBasic

open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic

set_option autoImplicit false

/-!
# All-order estimates for the Newtonian potentials of an annular density

The Newtonian kernel and each of its first derivatives are of every finite
differentiability order away from the origin, with

  `‖D^k N x‖ ≤ c_k ‖x‖₂^{-(1 + k)}`,   `‖D^k ∂_j N x‖ ≤ c_k ‖x‖₂^{-(2 + k)}`,

the kernel estimates behind `cor:CZ-harmonic`.  Consequently, if the density `g`
vanishes outside a set `A` separated from an open set `U` by `δ > 0`, then the
potentials `N * g` and `∂_j N * g` are of every finite differentiability order
on `U` and obey

  `‖D^k (N * g) x‖ ≤ c_k δ^{-(1 + k)} ‖g‖₁`,
  `‖D^k (∂_j N * g) x‖ ≤ c_k δ^{-(2 + k)} ‖g‖₁`   for `x ∈ U`,

with constants depending on the order `k` alone; this is the display
`eq:har-Ck`.  Specialising to the pressure geometry `U = B(x₀, ρ/2)` and
`A = B(x₀, 3ρ/4) \ B(x₀, 13ρ/20)`, the separation is `δ = 3ρ/20` (lem:cutoff).
-/

noncomputable section

namespace CKN.Foundation.Heat

/-! ### Smoothness of the first-order kernels -/

                                                                                      
                        
                                                                                             
                                                               
                                                                 
                                     
                                                            
                                      

                                                                           

                                                                                       
                                                                                     
                                                                                   
                              
                                                           
                     
         
          
      

                                                                                
                                                                                          
                
                                                    
                                                                 
                                      

                                                                                          
                                                                                     
                                                                                  
                                                                                   
                                                                   
                                                                                   
                                              
                                                     
                                                                       
                      
                                                                            
                                                                                     
                         
                                                                                        

                                                                                        
                                                                                  
                                                                       
                                                    
                                                                      
                                                                               
                                                                                   
                                                                   
                                                     
                                                                                      
                      
                                   
                                                                   
                                                                                 
                         
                              
                                                                 

                                                                                           
                                           
                                                                          
                                                                                           
                                                      
                                                                  
                                                                   
                                                       
                                                                     
                                                               
                                                         
                                                             
                                                                     
                                                                                      
             
                                                  
                                                                             

                                                                                         
                                           
                                                                          
                         
                                                                                           
                                                      
                                                                  
                                                                               
                                                       
                                                                                    
                                                               
                                                                     
                                                                              
                                                                 
                                                    
                                                  
                                                                         

                                                                       

                                                                                         
                                                    
                                                             
                                                              
                                                                  
                                                               

                                                                                     
                                                                                      
                                             
                                                                        
                                                                                    
                                                                           
                                             

                                                                                   
                                                                                       
                                                                  
                                                                        
                                                                       
                              
                                                                                       
                                             

                                                                                            
                                                                                   
                                                                                  
                                                                                         
                                                            
                                
                                                                   
                                                                  
                                                                                   
                                                  
                                                                
                                                                 
                                

                                                                                             
                                                                                
                                                                                  
                         
                                                                                         
                                                            
                                
                                                                               
                                                                  
                        
                                                                          
                                                  
                                                                
                                                                 
                                

                                                                                        
                        
                                                          
                                    
                                             

end CKN.Foundation.Heat
