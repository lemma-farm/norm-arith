/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.OUTimeDependent

/-! # Continuity at the zero outer-time endpoint of interpolation -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.Gaussian (standardGaussianMeasure)

namespace Critical2DKPZ.Ehrhard

/-- The Ornstein–Uhlenbeck average at time zero equals the original function. -/
theorem ouAverage_zero {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouAverage F x 0 = F x := by
  simp [ouAverage]

                                                                                         
                                                                 
                                                                         
                                                                

                                                                                                          
                                                                         
                                                       
                                                                   
                                                           
                                                                          
                                                                               
                                 
                                                                                        
              
                                                                   
              
                                                                                   
                            
                   
           
                                                         
                                                                                           
                                      

                                                                                               
                                                             
                                                                              
                                                       
                                                         
                                                                    
                                                                                 
                                              
                                                                    
                                    
                                                                                                    
                                                                    
                                                                                                          

end Critical2DKPZ.Ehrhard

end
