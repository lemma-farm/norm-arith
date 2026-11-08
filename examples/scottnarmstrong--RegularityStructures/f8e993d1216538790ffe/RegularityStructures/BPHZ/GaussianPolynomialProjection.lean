/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialGenerator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal projection onto polynomials of bounded degree

Polynomials of total degree at most `m` form a finite-dimensional subspace of `L²(γ)`.  Hence every
polynomial `f` splits as `f = h + (f - h)` with `h` of degree at most `m` and `f - h` orthogonal in
`L²(γ)` to all polynomials of degree at most `m` (`exists_orthogonal_part`).
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

                                          
                                            
                                                                         
                                                                                      
                       
                    
                
                                    
                                                                                   
                  
                                                                                  
                              
                                                                                  
                               
                                                                                            
                                                                                            
                        
                                              
                     
                
                                    
                                                                                   
                     
                                                                                  
                               
                                                                                            
                     
                                                                            

                                                               
                                                                  
                   
                 
                             
                                                                        
                                     
                                                                                          
                
                                                          
                                                                                            
                                                                   
                                                                     
                                              
                 

                                                                                              
                                            
                                                                     
                                                     
                                                                                        
                                                             
                                                      
                                           
                                                   
                                                                                           
                                                  
                                                                   
                                
                                                                     
                                                                                 
                                             
          

end RegularityStructures

end
