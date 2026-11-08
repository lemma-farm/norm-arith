/-
# Polynomial sup-norms on decreasing compact sets

This file supplies the compact-exhaustion transfer needed by approximation
arguments in the Crouzeix chain.  If `K n` is a decreasing sequence of
nonempty compact subsets of `ℂ`, then the polynomial sup-norms on `K n`
decrease to the sup-norm on their intersection.

The proof uses the extreme value theorem and Cantor's intersection theorem:
if the limiting infimum were strictly above the sup-norm on the intersection,
the corresponding closed superlevel subsets of every `K n` would be nonempty
and nested, hence would have a point in their common intersection.

## Main declarations

* `polynomialSupNorm_mono_of_isCompact` gives monotonicity when the larger
  set is compact.
* `polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact` identifies the
  sup-norm on the intersection with the infimum of the approximating norms.
* `tendsto_polynomialSupNorm_atTop_of_antitone_isCompact` is the sequential
  convergence form of the same result.
* `exists_polynomialSupNorm_convexThickeningApprox_le_add` and
  `tendsto_polynomialSupNorm_convexThickeningApprox_atTop` apply this
  approximation principle to the explicit open thickenings from
  `SmoothApprox.lean`.
-/
import Operator.Crouzeix.SmoothApprox
import Operator.Crouzeix.VonNeumann
import Mathlib
open Filter Polynomial Set

                                               
                                                             
                                                            
                                            
                   
                            
                                                    
                                                         
                                          
                                                     

                                                                             
                                                                         
                                           
                                                                       
                                                       
                                  
                                            
                                                                 
                              
                                    
                                                            
                                  

                                                                           
                                                                       
                                                              
                                      
                        
                                     
                                       
                                    
                                          
                                                    
                                           
                  
                     
                                          
                                                                      
                                           
                                                                                  
                   
                          
                                                               
                    
                  
                                                                
                                                       
                    
              
                                   
                    
              
                                                           
                                                     
                                                                                        
                                                    
                                                                               
                                  
                        
                                  
                                               
             
                             
                                                                                
                        
                           
                                                                   
                                                                 
                     
                                                                         
                                                                          
                                 
                     
             
                                  
                                                       
                                                             
                                      
                                                                
                                              

                                                                    
                                                          
                                                             
                                      
                        
                                     
                                       
                                                     
                                                   
                                                                             
                                                                  
                                                                           
                  
                     
                                          
                                                                                          
                                        

                                                     

                                                            
                                                  
                                                 
                                                       
                          
                                                                 
                                                                  
                                                    

                                                         
                                                               
                                                                       
                                                 
                                                                                       
                                                             

                                                             
                                             
               
                                                             

                                                                 
                                                       
                                                                             
               
                                                      
                                           
                                                      

                                                                          
                                       
                                                              
                                                                            
            
                                                        
                                       
                                                               
                                                                    
                        
              
                                           
                                                               
                                
                                                                   
                                            
                
                                                  
                                                 
                                                
                                                   
                          
                                         
                                                      

                                                                             
                                            
                                                              
                                                       
                                                                            
                                          
                                                                      
                                            
                                                            
           
                                                        
                                        
                                 
                      
                                                        
                                             
                   
                                                                             
                           
                           
             
                       
                                      
            
