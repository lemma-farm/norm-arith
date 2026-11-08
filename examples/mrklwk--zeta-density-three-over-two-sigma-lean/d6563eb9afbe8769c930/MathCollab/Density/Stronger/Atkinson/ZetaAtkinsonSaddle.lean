module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonPhase
public import Mathlib.Analysis.Real.Sqrt
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Unique nondegenerate saddle of the actual source carrier

The same real parameter b covers zero (the logarithmic main term)
and the two prospective Bessel carriers sqrt(n) and -sqrt(n).
A is the normalized height; the consumer substitutes T/(2*pi).
These exact calculus statements are not a stationary-phase estimate.
-/

noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSaddleRoot (A b : ℝ) : ℝ := (b + Real.sqrt (b ^ 2 + 4 * A)) / 2

                                                                                      

theorem atkinsonSaddleRoot_pos {A : ℝ} (hA : 0 < A) (b : ℝ) :
    0 < atkinsonSaddleRoot A b := by
  have h := Real.sqrt_lt_sqrt (sq_nonneg b) (show b ^ 2 < b ^ 2 + 4 * A by linarith)
  rw [Real.sqrt_sq_eq_abs] at h
  unfold atkinsonSaddleRoot
  linarith [neg_abs_le b]

theorem atkinsonSaddleRoot_equation {A : ℝ} (hA : 0 < A) (b : ℝ) :
    (atkinsonSaddleRoot A b) ^ 2 - b * atkinsonSaddleRoot A b = A := by
  have hs := Real.sq_sqrt (show 0 ≤ b ^ 2 + 4 * A by positivity)
  unfold atkinsonSaddleRoot
  nlinarith

                                                                 
                                        
                                                                             
                                                
                                                                                                    

                                                                                  
                                                                    
                                        
                                             
             
           
                                                      
                                                            
                                    
                                                                
                                                                    
                                                        
                                  
              
                           
            

                                                             
                                 
                                                                                  

                                                                         
                                     
                                                                           
                                                  
                                                            
                                                       
              
                           
                                                                                       
            
      

                                                                                      
                                                                          
                                                           
                                                                                 
                                       
                                                                                         
     

                                                                   
                                                                 
                                                                               

                                                      
                                                    
                                                                                 
                                                             


                                                                           
                                                                    
                                                                     
                                                            
                                                  
                                        
                                             
                                                                
                                                                          
                                                        
                                                                                   
                                                    
                                                              
              
            
      

                                                                               
                                                                            
                                                
                                                  
                                        
                                                                      
                                              
                                                                                                     

end MathCollab.Density.Stronger.Atkinson
