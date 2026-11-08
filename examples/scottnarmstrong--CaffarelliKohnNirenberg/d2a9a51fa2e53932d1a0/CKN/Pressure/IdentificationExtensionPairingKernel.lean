-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Measure.SliceDistributionTransport
import CKN.Pressure.Equation

/-!
# Second-order transport identities for translated mollifier kernels

This module records the mixed-second-order analogues of the first-order
mollifier transport identities of `CKN.Foundation.Measure.SliceDistributionTransport`.
In the elliptic-regularity analysis of Caffarelli--Kohn--Nirenberg (1982), the
pairing of a distribution with the countable family of translated mollifier
bumps is integrated by parts; the first-order identities handle the
divergence-form (first-derivative) slots, while the identities here handle the
second-derivative slots of `eq:leibniz-lap` and `eq:commute`.

Concretely, we differentiate under the reflected convolution: the integral of a
smooth `ψ` against the mixed second derivative `∂_i ∂_j` of the reflected kernel
`mollifier ε (x - ·)` equals the mollification of the corresponding mixed second
derivative of `ψ`.  The translation identities `spatialDeriv_sub_const` and
`mixedSecond_sub_const` reduce the reflected derivative to the translate of the
derivative, and the kernel vanishes outside its support ball.
-/

open MeasureTheory Metric
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

                                                                                 
                                                                        
                                                                   
                                                                                    
                 
                                                                                 
                                                                                        
                                  
                                                                                      
                                    
                                                                               
                                                                  

                                           
                                                                     
                                                                              
                                                                                      
                   
                                                                                   
                                                              
                                                    
                                                                
                                                         
                                                      
            
                                          
                         
            
                                         

                                                                            
                                                                           
                                                                               
                                                                             
                                                                               
                                                                                   
                                                                                     
                                                               
                                                                     
                                                              
                                                                    
                                            
                                                                
                                                                              
                           
                                                           
                                           
           
                                                     
                                                
                                                    
                                                               
                               
                                      
                                                                            
                                                                                  
                                  
                                                           
                                                   
                                                                                       
                        
                                                                               
                                                  
                                                                       
                                                                         
                                     
                                     
                                         
                            
                 
        
                      
                                       
                          
     

                                                                                
                                                                      
                                                                             
                                                             
                                                                                        

                                                                             
                                                                      
                                                                          
                                                  
                                                                                   
                                                                          
                                                                            
                                                        
                                                                 
                                     
              
                                                     
                                                                          
               
                                                          
                                                 
                           
                                                                                 
                                             
      

                                                                             
                                                                                
                                                                                 
                                                 
                                                         
                                                                                  
                                                             
                                                                                
                                                                
                               
                                              
                                             
                                                                   
                                                                           
                                                      
                                                                                    
                                                                  
                                                  
                                                                         
      
                                                              
                                                                                        
                                                                        
                                                
                                                
                                                               
                                                            
                    

end CKN

end
