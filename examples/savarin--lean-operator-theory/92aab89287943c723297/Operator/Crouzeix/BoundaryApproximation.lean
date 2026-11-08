/-
# Polynomial sup-norms on approximating boundaries

The explicit open thickenings from `SmoothApprox.lean` and the closed
thickenings from `CompactThickeningApprox.lean` use the same radius at every
stage.  The closure of the open thickening is exactly the closed thickening.
The maximum-modulus transfer in `BoundaryMaximum.lean` therefore identifies
the polynomial sup-norm on the open-stage frontier with the norm on the
compact control set.

Consequently, for a compact target, these frontier sup-norms converge to the
sup-norm on the target.  This is the scalar limit needed when a
smooth-boundary estimate is passed through the compact exhaustion.

## Main declarations

* `polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox`
  identifies the boundary and compact-stage norms.
* `tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop` proves
  convergence of the boundary norms to the target norm.
-/
import Operator.Crouzeix.ApproximationSupNorm
import Operator.Crouzeix.BoundaryMaximum
import Operator.Crouzeix.CompactThickeningApprox
import Mathlib
open Filter Polynomial Set

                                                         
                                  
                           
            

                                                                          
                                                                          
                                                                                    
                                                                         
                                                                 
                                                             
                                                                        
                       
                                                                      
         
                                                                

                                                                      
                                                             
                                                                       
                                                       
           
                                                                                 
                                          
                                                   
           
                                                                                
                                                                       
                                 
                                                                         
                                                  
                                            
                                                                      
                                                          
                     
                
                                                                                  
                                
