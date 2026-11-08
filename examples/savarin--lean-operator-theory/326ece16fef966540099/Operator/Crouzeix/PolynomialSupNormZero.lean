/-
# The zero case for polynomial sup norms on infinite compact sets

Normalization arguments for the Crouzeix--Palencia auxiliary estimates divide
by the polynomial sup norm.  This file isolates the complementary zero case:
a polynomial whose sup norm on an infinite compact subset of the complex plane
is zero must itself be zero.  Positive-radius closed disks are recorded as the
principal geometric specialization.

## Main declarations

* `polynomial_eq_zero_of_polynomialSupNorm_eq_zero` -- vanishing of the sup
  norm on an infinite compact set forces the polynomial to vanish.
* `polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero` -- the closed
  disk specialization.
* `polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite` --
  normalized sharp auxiliary bounds extend to every polynomial on an infinite
  compact set.
* `polynomial_auxiliary_bounds_of_normalized_closedBall` -- normalized sharp
  auxiliary bounds imply the corresponding bounds for every polynomial on a
  nondegenerate closed disk, including the zero sup-norm case.
-/
import Operator.Crouzeix.PalenciaSupport
import Operator.Crouzeix.VonNeumann
import Mathlib
import Mathlib.Topology.DiscreteSubset

open Polynomial ContinuousLinearMap

universe u

                                                                        
                                                                         
                                          
                                               
                               
                                                                   
                                                

                                                                             
                   
                                                       
                                                                  
                                                     
                                  
                  
            
                                 
                                                             
                                                     
                                                                              
                                                
                                  

                                                                        
                                 
                                                                  
                                           
                                                               
            
                                                                              
                                           

section AuxiliaryBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

                                                                             
                                                                          
                                                                       
                                                  
                                                                       
                                                            
                                                              
                                      
                                 
                               
                                                                     
                               
                                                               
                           
                                                               
                                     
                             
                                                        
                                         
                                         
                      
                                                                   
           
                                                                       
          
                                                       
                                                                                      
                            
                          
                                                            
                                                                  
                                                    
                                                                     
                            
                                                           
         
                                                                              

                                                                          
                                                          
                                                            
                                                                
                                   
                                      
                                                       
                               
                                                                     
                               
                                                               
                           
                                                               
                                                           
                             
                                                        
                                                            
                                                                         
                                                      
                                                     

end AuxiliaryBounds
