-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.PotentialLocalLpGrowth
import CKN.Pressure.DecompositionPotentials

/-!
# Local `L^{3/2}` membership and linear growth of the force potentials `p₇` and `p₈`

The two force terms of the local pressure decomposition `eq:pk`, estimated
in `lem:pk-bounds`, are

* `p₇ = ∑ⱼ (∂ⱼN) * (η fⱼ)`, a sum of first-derivative Newtonian potentials, and
* `p₈ = -∑ⱼ N * ((∂ⱼη) fⱼ)`, a sum of Newtonian potentials,

where `N = -newtonianKernel`.  In Lean, `pressureNewtonianDerivativePotential`
is convolution with `-∂ⱼN`, so the outer minus in `pressureP7` gives the positive
sign above.  The data use the cutoff `η` and force `f` of a suitable weak solution.  The
cancellation argument for the force feeds `p₇ + p₈` into the Liouville step of `ext:newtonian`,
which needs `p₇ + p₈` to be `L^{3/2}` on every round ball `euclideanBall 0 ρ` with local norm at
most `C * (1 + ρ)`.

This file assembles exactly that pair of statements from the single-potential estimates of
`CKN.Foundation.Euclidean.PotentialLocalLpGrowth`, with the constant an explicit finite sum of
the single-potential constants.  The hypotheses are per-slice: at a fixed time `s`, each of the
six data functions `(∂ⱼη) fⱼ(·, s)` and `η fⱼ(·, s)` is of class `L^q` with `6/5 ≤ q` and
vanishes off a closed ball.  The exponent range `6/5 ≤ q` contains the pressure exponent `3/2`
and the force exponents `q > 5/2` of `def:sws`.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! ### Negated finite sums of potentials -/

                                                                                               
                                                         
                                                                              
                                                                                  
                                                     
                                                                                 
                                                                       
                                                                               
                                                         
                                                                                 
                                                                                   
           
                                                                             
            
                                              
             
              
             
                                                                         
              
                         
                                                                                      

                                                         

                                                                                            
                                                                                      
                                                                                        
                                               
                                                

                                                                                            
                                                                                       
                                                                                        
                                                           
                                 

                                                                                              
                                           
                                                                             

                                                                                          
                                                                  
                                                                                         

                                                   

                                                                                   
                                                
                                          
                                                                                        
                                                                          
                                
                                                                    
                                            
                                                                           
                                                         
                                                                             
                                                        
                                                          
                           
                                                         
                                                                                  
                                                           
                                                           
                                                                                  
                                                          
                                            
                                                                                
                                                                                         
                               
                                               
                                                           
                                    
                                                                                     

                                                                                   
                                                
                                          
                                                                                        
                                                                                      
                                                                    
                             
                                                                           
                                                         
                                                                             
                                                        
                                                          
                           
                                                                     
                                                                   
                                                           
                                                                       
                                                                   
                                                          
                                                        
                                                                 
                                                                                 
                         
                               
                                                           
                                            
                                    
                                                                                     

                                                                             

                                                                                              
                                                                                           
                                     
                                                         
                                                                                        
                                                                                       
                                                                     
                           
                                                                           
                                
                                                                     
                                            
                                                                 
                                    
                                                         
                                                                   
                                    
                                                        
                                                                                               
                                                                               
                                                                               
                                                    
                                                                 

                                                                                            
                                 
                                                       
                                                                             
                                                                                 
                                                     
                                                    
                        

end CKN.Foundation.Euclidean
