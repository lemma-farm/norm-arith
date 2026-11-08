module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative
public import PDEFoundation.Sobolev.WeakDerivative.Affine
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
public import Mathlib

/-!
# Affine transport for convex-domain smoothing

Precomposition by each fixed convex-approximation sampling map transports weak
partial derivatives and weak gradients with the exact affine factor `1 - ε`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace HasWeakPartialDerivOn

                                                                         
                                                              
                               
                             
                                      
                                  
                                         
                            
                                        
                               
                                 
                             
                                                  
               
                                                           
                    
                                   
                                               
                       
                  
            
             
                                                     
                                                          
                               
                        
         
                                                           
                                                  
           
                                       
                        
                                        
                    
                                       
                             
                    
                                     
                                                        
                                                             
                                              
                                
                 
                               
                                      
                                       
             
                                                
                                   
                                               
                                 
        
                             
                                          
                                              
                                                      
                                          
                                     

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

                               
                                                   
                               
                             
                                      
                                        
                                   
                            
                                        
                               
                                 
                       
                                                  
                 
                                                             
         
       
                                  
                            

end HasWeakGradientOn

end PDE
