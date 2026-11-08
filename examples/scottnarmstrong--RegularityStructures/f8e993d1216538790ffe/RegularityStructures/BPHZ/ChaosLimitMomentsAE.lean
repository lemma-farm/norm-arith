/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.WhiteNoiseChaosMoments

/-!
# Moment equivalence for almost sure limits of finite-chaos random variables

If `Rₖ` are (almost surely) cylindrical polynomials of degree at most `m` of a white noise,
`Rₖ → X` almost surely and `sup_k E Rₖ² < ∞`, then `E X^(2p) ≤ A * (E X²)^p`, with the constant
`A = A(m, p)` of `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`.

The proof upgrades almost sure convergence to `L²` convergence: hypercontractivity bounds
`E Rₖ⁴`, hence `E (Rₖ - X)⁴`, and an almost surely convergent sequence bounded in `L⁴` converges
in `L²` (`tendsto_integral_sq_of_ae_tendsto_of_integral_pow_four_le`, by truncation at a level
`M`: the truncated part converges by dominated convergence and the tail is at most `D / (4 M)`).
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

                                                                                  
                                                                 
                                                 
                                                
                                      
                      
            
                       
                                            
                                      
                                           
            

                                                                                       
                             
                                                                             
                                                                                        
                                               
                                                    
                                     
                                                            
                                                          
                                                                           
                                                                    
                                                                      
                                                          
                                                                
                                                            
                           
            
                                     
                                  
                                         
                                           
                                                              
             
                                                                             
                                                                
                                                                              
                                                                 
                          
                                                
                                                                           
                               
         
                                       
                                                                
                              
                                                    
                                             
                 
                                                                          
                            
                    
                                     
                                                          
                                        
                                
                                                                   
                                                    
                                                                             
                                       
                                                                          
                                                              
                     
                                                           
                        
                                     
          

end RegularityStructures

end
