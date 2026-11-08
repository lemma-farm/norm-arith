-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InversePolynomial
public import RothschildStein.G2.PolynomialCalculus
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Polynomial inversion is smooth (BB Proposition 3.7, p. 98). -/
theorem contDiff_inv : ContDiff ℝ (⊤ : ℕ∞) G.inv :=
  contDiff_pi.mpr fun j => contDiff_eval (G.inversePolynomial j)

                                                                   
                      
                                                                                  
                       
         
                                                    
                                           
                                                         
                                                          

                                                     
                              
                                                  
                                                       
                                                                                                   

                                                                         
                               
                                                               
                                                                                        
                                 
                                           
          

                                                                                              
                                                        
                                                                                        
                                                                            
                                    
                                          
                                     
                                                      
                                                                
                                                                        
                                         
                                                                                  
                             
                                                                                    
                                                       
                                                   
            
                                         
         
                                    
      

                                                                 
                               
                              
                                                                     
                           
         
                                                                  
                                            
                                                                                      
                                        
         
                            
       
      

end RothschildStein.G2
