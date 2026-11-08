/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Integrals of products of two centred parabolic powers

For a centre `c` and exponent `a`, `singularPow a c w = s(c - w)^(-a)`.  If `0 < a, b < 5` and
`a + b > 5`, the product `singularPow a p * singularPow b q` is integrable and its integral is
at most `C * s(p - q)^(5 - a - b)` (the whole-space convolution estimate of [Hai14, Lemma 10.14],
in the form with two arbitrary centres, together with integrability of the integrand).

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- The parabolic power weight `s(c - w)^(-a)` centred at `c`. -/
def singularPow (a : ℝ) (c w : SpaceTime) : ℝ := torusParabolicSize (c - w) ^ (-a)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem singularPow_nonneg (a : ℝ) (c w : SpaceTime) : 0 ≤ singularPow a c w :=
  Real.rpow_nonneg (torusParabolicSize_nonneg _) _

                                                                                        
                                                                                             

                                            
theorem singularPow_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p q w : SpaceTime}
    (hp : 0 < torusParabolicSize (p - w)) (hq : 0 < torusParabolicSize (q - w)) :
    singularPow a p w * singularPow b q w ≤
      singularPow (a + b) p w + singularPow (a + b) q w :=
  torusParabolicSize_rpow_neg_mul_le ha hb hp hq

                                                                                  
                                                                                        
                                                                   
                                                                
                                                                                    
                                                                              
                                             
                                              
                                                  
                                                   
                                                     
                                                     
                                        
                                                      
                                                                           
                                        
                                                        
                                                         
        
                                                   
                                                                
                                                            
                 
                                 
                
                                           
                                                        
                                                                               
                                           
                                                         
                                                            
          
                                                      
                                                                  
                                                                     
                   
                                   
                  
                                                                                         
                                                  
                                                                                           
                                                  
                                                                                 
                        
                                              
                  
                            
                               
                               
              

                                                 
                                                                         
                                
                                                                         
                                                      
                                                      
                                                 
               
                                           
                                           
          

                                                                                            
                                
                                                                                       
                                                  
                                                                        
                                                                   
                                                    
                                                            
                                          
                                     
                                     
                                                                                    
                                                                 
                                                                 
                                                                                
            
                                                                            
                                                                                   
               
                                             
                                     
                            
                                                      
                                                      
                                                              
                                                       
                                                       
                                                     
                                                      
                                                                                
                                                                                       
                                          
                                                                               
                    
                                                                               
                    
                                                                              
                                                              
                                                                               
                                                                                           
                
                                        
                                                                                        
                                                                                     
                   
                                                                  
                                                                                           
                                                                       
                                                                    
                                                                             
                                                                 
                                                                
                                  
                                                
            
                                                                    
                                                                                           
                                                 
                 
                                                                         
                                             
                                                                   
                                                                   
                                                                        
                                                                        
                                                     
                                                     
                                                            
                                          
                                                            
                                          
                                                       
                                                       
                                                  
                                                                                
                                                  
                 
      
                                                            
                                                                      
               
                                                 
                                                   
                                                          
                                                           
                                                                            
                                                   
                                                                          
                                 
                                                         
                                                   
                                                   
                                                              
                           
               
             
          

end RegularityStructures

end
