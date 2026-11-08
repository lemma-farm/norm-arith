/-
# Polynomial Cauchy representation from resolvent mass

The all-polynomial operator Cauchy formula on a smooth contour follows
algebraically from its constant-polynomial case.  The resolvent splitting

`p(A) R_A(z) = p(z) R_A(z) - (p / (X - z))(A)`

leaves a divided-difference remainder which is polynomial in `z`.  Its
integral around any closed smooth parametrized boundary vanishes term by
term.  Thus a single normalized resolvent-mass identity supplies the full
polynomial representation required by the Crouzeix--Palencia assembly.

## Main declarations

* `contourIntegral_aeval_divByMonic_X_sub_C_eq_zero` -- the evaluated
  divided-difference remainder has zero closed-contour integral;
* `polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass` --
  resolvent mass implies the normalized polynomial operator Cauchy formula.
-/
import Operator.Crouzeix.ProductContour
import Mathlib
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

                                                            
                                          
                                                                      
                                                       
                                                        
             
         
                                                                                  
             
                                                                      
                               
         
                
             
                                           
                                                                
           
                                                                                  
                                           
                                                              

                                                                           
                                                                         
                                                         
                                   
                                            
            
                                                              
                                       
                        
                                             
                                                      
                                                             
                                               
                                                                    
               
                                                                                      
                                                                          
                                                             
                                               
                                                                    
               
                                                                                      
                                                  
                                                                     
                                                                  
                                                    
                  
                                    
              
                                       
                                                                  
                 
                                                          
                                    
                
                                 
                                                               

                                          
                                                                      
                                                                            
                                                           
                                                        
                                                                     
                   
                                    
                                                 
                                     
             
                                      
                                                 
                                                    
                                              
                                                      
            
                                                                       
                    
                                              
                                                                         
                                     
           
           
                        
                                        
                                          
                            
             
                                             
                 
                                                                 
                                              
                                                     
                                   
                                                          
                                                    
             
                                     
                                                        
                                                 
                                 
                                             
                                                                  
             
                                                                                    
                                                                               
                                                                   
                                            
                                                                         

                                                                           
                                                                             
                                                                              
                                                                        
                                                
                                                         
                                                                
                                                
                        
                          
                                 
                       
                                                        
                                   
                                           
                                   
                                                             
                                                                             
                               
                                                                       
                                            
                                                         
                                           
                                                                
           
                                                                                  
                                                                  
                                                                   
                               
                                            
               
                                               
                                                      
                                                   
                                                    
              
                                                                  
                                                   
             
                                
                        
                                                 
                                               
                                                 
                                         
           
                                                                            
                                                           
                     
                                         
               
                                                                    
                               
                                                                          
                                                     
                                             
                          
                                         
             
                                        
                                                 
                                                     
                                                               
                                                                    
                              
                
                                               
                      
                                                  
                                                
                                                             
