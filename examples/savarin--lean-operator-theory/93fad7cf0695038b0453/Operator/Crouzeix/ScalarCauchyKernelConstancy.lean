/-
# Constancy of the scalar Cauchy kernel on a convex carrier

For constant boundary data, the scalar Crouzeix companion is the normalized
Cauchy winding kernel.  Its derivative in the carrier is the contour integral
of `(sigma - z)⁻²`, which vanishes because this integrand has the global
primitive `-(sigma - z)⁻¹` along the boundary.  The carrier is open and
preconnected by strict convexity, so the zero-derivative theorem makes the
kernel constant throughout it.

Consequently, the stagewise winding hypothesis in the scalar-companion route
need only be checked at one point of each carrier.

## Main declarations

* `crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier` --
  the constant-data companion has zero derivative in the carrier;
* `crouzeixScalarCauchyKernel_eq_of_mem_carrier` -- the scalar kernel has the
  same value at every two carrier points;
* `crouzeixScalarCauchyKernel_eq_one_of_basepoint` -- one normalized
  basepoint propagates winding normalization through the carrier.
* `contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier` -- the scalar
  Cauchy contour vanishes at every exterior point;
* `crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier` -- the
  corresponding exterior winding normalization.
-/
import Operator.Crouzeix.ScalarCompanionPlemelj
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex Set
open scoped Interval Real

                                                                           
                                                                       
                                                          
                                                                           
                                                                   
                                                                             
                                                         
                 
                                                                
                                                     
                                             
                            
                                       
                                                   
                           
                
                                                                   
                                   
                                                         
                                             
               
           
                                                                                    
               
                                                           
                                                                  
                                   
                              
           
                    
            
                                             
                                                                  
             
                                                                                    
                              
                               
                                                                 
                              
                     
                                                                
                                 
                                               
                                                                          
                      

                                                                        
                  
                                                    
                                          
                                                       
                                        
                                              
                  
                                                            
                                                    
                                                       
                                              
                                                    
              
                      
                                                                
                                      
                              
               
                                                                         
                 
                                                            
                                                                    
                                                   
                                                                               

                                                                         
                 
                                                      
                                                                 
                                                    
                                                                     
            
                                                     
                          

                                                                        
                                                                           
                                                                          
                                        
                                                                  
                                        
                                      
                                                    
                                   
                                                    
                                             
                           
                                                      
                                 
                          
                                                      
                               
                                      
                             
                                                    
             
            
              
                     
                      
                                                             
                                  
        
                                
                                                       
                                    
                                        
                                           
                            
                         
            
                                      
                            
                                                       
                        
                                  
            
                       
                                                                 
              
                 
                                                        
                                            
                                                   
                                     
               
                                                    
                                  
                                                          
                                                                
                                     
                                                              
                              
                                                      
                                     
                                                  
                 
                                                      
                                             
                                                   
                                
          
                        
               
                                                       
              
             
         
                                                  
                                       
            
                                           
                                                                
           
                                                      
                                     
                             
                                                               
                              
                                     
                                                              

                                                                          
                             
                                                                     
                                        
                                      
                                                
                                   
                                                                
                       
