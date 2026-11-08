/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

                                                              
public import RegularityStructures.Analysis.Kernel.Parabolic

/-!
# The time-derivative bound for the parabolic kernel

[Hos25, Definition 2.6 (iv)] (arXiv:2310.07396v2) asks for
`|∂_t Q_t(x, y)| ≤ C t⁻¹ t^{-5/4} G(t^{-1/2} z₀, t^{-1/4} z')` with a rapidly decaying `G`.
For `parabolicKernel` this follows from exact scaling and the decay of `k_1, k_1', g_1, g_1'`:
`parabolicKernel` is differentiable in `t` with derivative `parabolicTimeDeriv t z`
(`hasDerivAt_parabolicKernel_time`), and
`|parabolicTimeDeriv t z| ≤ t⁻¹ t^{-5/4} parabolicTimeProfile (S^{t^{-1/4}} z)`
(`abs_parabolicTimeDeriv_le`), where `parabolicTimeProfile` is an explicit profile built from
`|k_1|, |g_1|` and `|k_1 + u k_1'|, |g_1 + u g_1'|`, with rapid decay in every coordinate
(`parabolicTimeProfile_decay`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

                                                               
                                                          
                              
                                                                                     
                        
                                                                                           
                                                                                            
                                                                                           

                                                                                         
                                  
                                                                                    
                       
                                                    
                                                                                         
                                  
                                    
                                                                                       
                                                                                        
                                                                                       

end RegularityStructures

end

public section

open Real

namespace RegularityStructures

                                                                                   
                                                                              
                                                                    
                                                                                         
                                              
                        
                                           
                                                                                   
                                    
            
                                                    
       
        
                         
                                                                           
      

                                                   
                                                                                        
                                                                                        
                                                           
                                                                        
                                                                                 
                                            
                                                                                 
                       
                                                                                    
                              
                                                                                            
                                                                                      
                                  
                                    
                       
          
                                                                             
                       
                        
                                                   
                                                                             
                                      
                                                                  
                                                                 
                                                       
                                                            
          
                                 
      

                                                                                    
                 
                                                 
          

                                               
                                                              
                 
                                                                     
          

                                                                             
                                  
                                                                             
                              
                                                                                                    
                                                  
                                                  
                                        
                                                                                                    
           
                                                                                       
                                                                     
                                                                                                  
           
                                                                                     
                                                                     
                                                  
                                                                                     
                                                                 
                      
              
                                                  
                                                                                     
                                                                 
                      
              
                                
                                  
                                                      
                                                    
                          
              
       
           
                                                                                         
                                                                   
                                                                           
                                                                                   
                                                        
                                                                                           
                                                                                                     
                                                    
                                                                                               
                                                                                             
                                                                                             
                                                
                                        
                    
                                          

                                                   
                                                               
                                    
                  

                                                  
                                                                           
                                                                                           
                                                
                                                                  
                                                                               
                                                                                        
                                                                                               
                                                                                       
                                                                                            
                                                                         
                                                                              
                                                       
                    

                                                                      
                                            
                                                           
                                                                            
                                              
                                                              
                                             
                                                              
                               
                               
                               
                               
                                                                          
                          
                                                                                
                                                                       
                                                                    
                                                                 
                                                                      
                                                                         
                                                                            
                                                                
                                                                
                                                                                             
                                                           
            

end RegularityStructures

end
