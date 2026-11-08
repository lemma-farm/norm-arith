/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialProjection
public import RegularityStructures.BPHZ.GaussianPolynomialCalculus

/-!
# Reverse Poincaré inequality for Gaussian polynomials (algebraic form)

For a polynomial `f` of total degree at most `m`, the Dirichlet form is bounded by `m` times the
`L²(γ)` norm squared, with no dependence on the number of variables:
`∑ i, E[(∂_i f)²] ≤ m E[f²]` (`sum_gaussExp_sq_pderiv_le`).

The proof is by induction on `m`.  Split `f = g + h` with `h` the `L²(γ)` projection of `f` onto
polynomials of degree at most `m - 1`.  The generator satisfies `gaussGen g - m g` of degree
below `m`, hence orthogonal to `g`, so `E[g L g] = m E[g²]`, and the cross terms vanish by
symmetry of the generator.
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

                                                                       
                 

                                                                   
                                          
                         

                                                                              
                                                                                             
                                                                        
                  
           
              
                                                                  
                
              
                                                       
                          
                                             
                                                                         
                                                          
                                                 
                                               
                                                 
                                                                        
                                                   
                                                                                           
                                
            
                                                                                     
                                                        
                                               
                                                                              
                                                                             
                        
                                                                          
                                           
                                         
                                                       
                      
                                                                                     
                                        
                                                                                     
                                        
                                                                                   
                            
                           
                        
                                                              
                           
                         
                                                                            
                                                                    
                                                                              
                   
                                    
                                              
                     
                  

end RegularityStructures

end
