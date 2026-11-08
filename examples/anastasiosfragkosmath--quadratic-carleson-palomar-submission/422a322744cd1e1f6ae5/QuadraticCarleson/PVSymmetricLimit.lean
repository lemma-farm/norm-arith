/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.PrincipalValueDistribution
import Mathlib

/-!
# Symmetric truncations of the principal-value distribution

The direct cancelled pairing defining `p.v. (1 / x)` is the limit of the
ordinary integrals over `{x | ε < |x|}` as `ε → 0+`. The proof first removes
the constant term on a symmetric annulus using the measure-preserving
change of variables `x ↦ -x`. The remaining error is the integral of the
bounded cancelled integrand over `[-ε, ε]`, yielding an explicit bound by
`2 * ε` times the first derivative Schwartz seminorm.
-/

open MeasureTheory Set Filter
open scoped SchwartzMap Topology

namespace QuadraticCarleson

                                                                    
                                                               
                                              
                              
                                                                   
                                                               
                                                    
                                                   
            
                                                                                   
              
                      
                              
                           
                      
      
                                                                            
                                                     

                                                                   
                                                             
                                                                     
                                 
                                  
                                                                             
                                                     
                                              
                                                            
                                                                  
                                                                
                                                         
                                 
                                            
                                                     
                        
                                   
        
                                                                   
                                       
                               
                             
                                                        
            
                                                         
                                                             
         
               
              
                                      
                            
                      
                      
                  
                             
                                           
                                                                
                                     
                                                                                    
                                                                 

                                                                         
                                       
                                                                 
                                 
                                                            
                                                              
                                              
                                                              
                                                
              
                                                                
                                                   
         
               
              
                           
                                        
                                                  
                      
                      
                      
                                      
                                                                             
                                                       
                                                                 
                                                                 
                       
                                                      
                                  
                                
      

                                                                     
                                                             
                                                                         
                                 
                                                              
                                                
                                                                
      
                                                          
                                                                  
                                                             
                                                           
                                                  
                                                                             
          

                                                                        
                                                                        
                                                        
                                                               
                                         
                                             
                                                                          
                                                      
                                              
                                                                     
                                         
                                                               
                                                                
                                             
                                         
                                                                  

end QuadraticCarleson
