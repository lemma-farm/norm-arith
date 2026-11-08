/-
# The auxiliary product bound for aligned circles and normal polynomial values

The fixed-domain auxiliary product estimate against the closed numerical
range is false for arbitrary containing circles: an off-center contour can
sample `p` at a point unrelated to the control set.  This file records a
correct strengthened branch.  If the individual value `p(A)` is star-normal
and the circle center belongs to `closure (numericalRange A)`, spectral
calculus controls `p(A)` by the numerical-range sup norm, while center
membership controls the scalar value appearing in the affine-circle
auxiliary identity.

## Main declarations

* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval`
  proves the literal L4.2e product conclusion when the individual value
  `p(A)` is star-normal.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal`
  specializes the result to a star-normal operator.
-/
import Operator.Crouzeix.AffineAuxiliary
import Operator.NumericalRange.Bounded
import Operator.SpectralSet.Normal
import Operator.SpectralSet.SpectrumInNR
import Mathlib
open Complex Polynomial Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

                                                                               
                                                                              
                                                               
       
                                                                                           
                                   
                                        
                                                            
                                           
                           
                                             
                                      
                                                         
                                                                
                                                  
               
                                       
                                             
                                      
                                                             
                           
                         
                     
             
                                                           
                                                           
                                                  
                                          
                                                                    
                                                  
                                         
                                    
                                                           
                                                                             
             
      
                           
                                                         
                                
                                                           
                     
                                                            
                                                  
                
                                        
                                   
                                                                  
                  

                                                                          
                                                                           
                                                    
       
                                                                                     
                                                    
                                        
                                                              
                           
                                             
                                      
                                                         
                                                                
                                                          
                             
                           
                  
       
                                                                                           
                 
