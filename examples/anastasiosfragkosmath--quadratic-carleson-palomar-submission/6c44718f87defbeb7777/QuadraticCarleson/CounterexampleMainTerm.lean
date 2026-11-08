/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.CounterexampleBohrPhase

/-!
# A finite dyadic main-term level set for the negative endpoint

The parameter `L` is the paper's base-two logarithm of `A`.  We keep exactly
the half-open exponent windows `N * k + L ≤ n < N * k + L + N`, with `k` in
`paperBohrIndices N`.  Natural ceilings implement those windows without any
rounding enlargement.  The supremum is taken over the actual complex sums
`harmonicPhaseSum`, not over Bohr membership or an assumed operator estimate.

The full level set has an extended-real Lebesgue-measure lower bound.  We
also give the real-valued measure bound after localization to `[0, N + 1]`,
which already contains the entire translated Bohr set.  No finiteness of an
unlocalized level set is tacitly assumed.  These are main-term estimates;
passing to the singular integral requires the separate analytic error bounds.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

set_option autoImplicit false

                                                                              
                                                                          
                                       
                       
                                                          

                                                                          
                                       
                              
                                 
                                         
                                                       

                                                                        
                                                                             
                                                                         
                                                         
                                                          
                                                          
                                                          
                                                
                                               
                                                                                
             
             
                                                                                
             

                                                                              
                                                                            
                                           
                                                               
                                                           
                                 
                                                          
                                                
                            
             
                               
             
                               
             

                                                                           
                                                                        
                                                                      
                                      
                                                          
                                                      
                                             
                                             
                                           
                       

                                                                        
                                                                                
                                                           
                                           
                                                                  

                                                                                 
                     

                                                                             
                                              
                                                            
                                  
                                                      
                                                                      

                                                                            
                                                                                    
                                                                     
                                                             
                                                          
                                                       
                                                                 
                                                                                  
                                                                  
                                                               
                                  

                                                     
                                           
                                                 
                                                                         
                                 
            
                                                          
                    
                                                                           
                                              
              
                                         
                                                              
                          
                                   
                           
                                                      

                                                                 
                                                      
                                  

                                                               
                                                  
                                                                     

                                                                            
                          
                                                                        
                                     
                                                            
                                                                        
                                          
                                                            
                     
                                                                        
                                                  
                              
                     
                                                                    
                   
                     
             
                              
                           
                            
                             

                                                                      
                    
                                
                                                            
            
                                             
                                              
                                                               
                                                    

                                                                         
                                                                 
                                                                          
                                                                
            
                                                                                 
                                
                                                     
                                                
                                                          

                                                                             
                                                                             
                                                       
                                                       
                                                              
                                                                     
                                                           
                                                                             
      
                                                                    
                                                                                    
                                                                         
                                                                             

                                                                         
                                                                         
                                                                  
                                                       
                                             
                                              
                                                               
                                          
                                 
                                                           
                                                       
                                                         
                                                    
                                                              
                                                        
                                                                   
                                   

end QuadraticCarleson
