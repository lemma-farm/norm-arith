/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.OUJointRegularity
public import Critical2DKPZ.Ehrhard.OUTimeDependent
public import Critical2DKPZ.Ehrhard.GaussianLinearAverageBounds

/-! # Bounds for space and time derivatives of bounded smooth OU inputs -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace Critical2DKPZ.Ehrhard

/-- Ornstein–Uhlenbeck averaging preserves a uniform absolute bound. -/
theorem abs_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hF : ∀ y, |F y| ≤ B) (x : Fin n → ℝ) (t : ℝ) : |ouAverage F x t| ≤ B :=
  abs_gaussianLinearAverage_le
    (fun z y => Real.exp (-t) • y + Real.sqrt (1 - Real.exp (-2 * t)) • z) hF x

                                                                            
                                                              
                                                                
                                                                            
                                                     
                                                                            
                              
                                                                 
                                           
                                               
                                                                                            
                                                              
                                                                                
                                                              
                                                  
                                                                             

                                                                                                          
                                                            
                                                                        
                                     
                                                                                
                                          
                                                           
                                                                                
                                                                        
                                                                                                      
        
                                                                  
                                                                                                     
                                                                     
                                                                                                    
                                                         
                                                                                             
                                      
                                    
                                                     
      
                                      
                                                                                  
                                                                       
                         
                                     
                  
                                      
                                                                                  
                                                                       
                                                                                     
                                      
                                                               
                                                     
                    

                                                                                          
                                                                  
                                                              
                                       
                                             
                                                  
                                     
                                                                     
                                          
                                               
                                                      
                                                                                           
                                                  
                                  
             
                                                                
         
                                                                                
                                                                      
                                              
        
                                                                              
                                       
                                                                     
                               
      
                                            
                                                  
                                                                            
                                            
                               
                      
                                                                               
                                             
                                                                    
                                                             
                                

                                                                          
                                                                          
                                                                      
                                                                          
                                          
                                                               
                                                                                
                                          
                                                                                            
                                             
                                                                      
                                                                                    
                                                                
                                                                         
                                           
                                                                                       
                                                  
                                                
      
                                                                                      
                                               
                                                                                   
                       
                             

end Critical2DKPZ.Ehrhard

end
