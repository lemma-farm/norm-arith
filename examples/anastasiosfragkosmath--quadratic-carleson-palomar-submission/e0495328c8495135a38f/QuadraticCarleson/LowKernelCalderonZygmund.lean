/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.LowKernelDerivative
import QuadraticCarleson.CalderonZygmundBadPart
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Calderón--Zygmund regularity of the low oscillatory kernel

This file turns the derivative estimate for the paper's low kernel into the
kernel-difference estimate used on a mean-zero Calderón--Zygmund atom.  The
mean-value theorem is applied on the segment joining `x - y` and `x - z`.
When `y` belongs to the interval centered at `z` and `x` is outside its
triple, every point of that segment stays quantitatively away from zero.
-/

open MeasureTheory Set

namespace QuadraticCarleson

set_option autoImplicit false

                                                                          
          
                                  
                                                       
                                              

                                                                            
                                                 
                                                      
                              
                                         
                                     
                               
                                                                            
                                   
                                         
                                               
        
                                                 
                                             
                               
          

                                                                       
                                                       
                                                  
                                     
                          
                       
                        
         
                            
        
                            

                                                                         
                          
                                                     
                                
                                         
                                   
                                     
                           
                                                                  
                                          
                               
                                                                  
                                         
                                                            
                                             
      
                                                                             
                                                               
            
                                                                 
                                 
              
                                                                          
                                           
                       
          

                                                                           
              
                                                    
                                                      

                                            
                                   
                            
                  
                                                                                 

                                                                      
                                                                          
                                           
                                      
                              
                                         
                                     
                                      
                                          
                                                         
                                               
                
                
                              
                                                              
                                                     
            
                                                           
              
                                        
                        
                                                                 
                          
               
             
                                   
              
                                                                            
                               
                   
                                                              
                           
              
                                        
                        
                                                                 
                          
               
             
                                   
              
                                                                        
                               
                                     
                                             
                                                                     
                                           
        
                                                 
                                                 
                                       
                                                       
                                                                            
              
                                                                
                           
                                 
            
                                                                  
                                                  
                                
                        
      
                 
                                                               
                                       
                                                           
                                                             
                                                           
          

                                                                         
                                                             
                                         
                                      
                         
                
                                                
                                                  
                                            
                  
                                                       
                               
                                 
                                           
                                              
                                                        
                                         
                                     
                                                  
                                       
                                                
                                           
                                                               
                                                  
                                                                         
         

end QuadraticCarleson
