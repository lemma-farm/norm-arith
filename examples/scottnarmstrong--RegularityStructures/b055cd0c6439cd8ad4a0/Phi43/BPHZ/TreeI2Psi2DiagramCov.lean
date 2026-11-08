/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramInner

/-!
# The kernel increment and the covariance weights

`i2Psi2Increment K x y w = K(y - w) - K(x - w)` is the kernel `δK_x(y, w)` of [Hai14, (10.39)].
A covariance `Q` with `|Q u| ≤ B s(u)^(-1)` satisfies the flipped bound
`|Q(w - g)| ≤ 2 B s(g - w)^(-1)` (`abs_cov_flip_le`), and its square
`Q(w - g)² ≤ 4 B² s(g - w)^(-2)` (`sq_cov_flip_le`), so that it can be paired with the weights
of `TreeI2Psi2DiagramInner`, which are written with `s(g - w)`.
-/

@[expose] public section

namespace RegularityStructures

/-- The kernel increment `δK_x(y, w) = K(y - w) - K(x - w)` of [Hai14, (10.39)]. -/
def i2Psi2Increment (K : SpaceTime → ℝ) (x y w : SpaceTime) : ℝ :=
  K (y - w) - K (x - w)

end RegularityStructures

end

public section

namespace RegularityStructures

                                                                                                  
                                        
                                                      
                    
          

                                    
                                                                                
                                        
                                                                              
                                                
                                                                               
                                                                                   
                                                                    
                                          
                                                                          
                                                            
          

                                                                     
                                                                
                                                     
                                                                      
                                          
                                                                       
                                                                                   
                            
                                           
                                                                                  
                         
                              
                                                                      
                                                                                            
                    

                                                                 
                                                               
                                                     
                                                                      
                                          
                                                                             
                                    
                                                                                      
                                        
                                                                                                         
                                                  
            
                   
                                                                                  
                                                                            
                       

theorem measurable_i2Psi2Increment {K : SpaceTime → ℝ} (hK : Measurable K) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y) :=
  (hK.comp (measurable_const.sub measurable_id)).sub (hK.comp (measurable_const.sub measurable_id))

                                               
                                             
                                                     
                                                                    
                                    
                                                             
                   
                                                                      
                                        
                                                                                             
                                                  
            
                   
                                                                  
                                                                  
                       

                                                         
                                                                                                
                                          
                                                                                   
                                                                                            
                    
                                 
                                                                                        
                              
                                                                          

end RegularityStructures

end
