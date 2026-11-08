-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module
public import Mathlib
public import Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import AVenhance.Infra.FaaDiBruno.Seminorm
/-!
# Sharp composition bounds

The analytic composition estimate is proved from the ordered-finpartition
Faà di Bruno formula, keeping the paper's coordinate seminorms and constants.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open MeasureTheory
open Homogenization

local instance realMeasureSpace : MeasureSpace ℝ := Real.measureSpace

                                                                         
                                                                       
                                     

                                                                                 
                                                                            

                                                              
                         
                                                              
          
                                   

                                                             
                                                                 
                                                                            
                                                                  
                                             
                         

                                                                                     
                                                      
                                                                  

                                                           
                                            
                                                              
                      
                                                                                      
                      
                                             
                                                         
                      
           
                                                                            
                       
                                                          
                                                             
                     
                                                                    
                                         
                     
                                                                                      
                                     
                                         
                 
                                                                  
                                            
                                                                                      
               
                                    
                                                              
                                                     
                                                           
                                              
                                                                              
                                      
                                                                                       
                  
                          
                                                                            
                                                               
                                                 
                            
                           
                     

                                                                  
                                            
                                                            
                                       
                                                                                    
                      
                                          
                                                                               
                  
                                                                            
                                                 
                                            
                                                             
                                              
                                                                  
                                               
                                      
                                                                                    
                                           
                          
                                                                                               
                                                            
                               
                                       
              
                                                        
                                                              
                                                                        
                   

                                                                                
                                                                
                                                                            
                                                                         
      
                                                                
                               
                             
                
                                       
                                                   
           
                 
                      
                             
                                                                          
                           
                                                                 

                                                                          
                                                         
theorem derivativeSup_le_of_snorm_le {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F)
    {R C : ℝ} (hR : 0 < R)
    (hs : snorm f n R ≤ ENNReal.ofReal C) :
    derivativeSup n f ≤ ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
  let w : ℝ := (n + 1 : ℝ) ^ 2 / n.factorial
  let r : ENNReal := ENNReal.ofReal R
  let a : ENNReal := ENNReal.ofReal w * r⁻¹ ^ n
  have hw : 0 < w := by dsimp [w]; positivity
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hrtop : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hw).ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hrtop))
  have hatop : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hr0))
  have hs' : a * derivativeSup n f ≤ ENNReal.ofReal C := by
    simpa [snorm, w, r, a, mul_assoc] using hs
  have hmul := mul_le_mul_left hs' a⁻¹
  have hleft : a⁻¹ * (a * derivativeSup n f) = derivativeSup n f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  have hfactor : a⁻¹ * ENNReal.ofReal C = ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
    have hwpos : 0 < w := hw
    have hreal : w⁻¹ * R ^ n * C = C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
      dsimp [w]
      field_simp
    have hpow : (r⁻¹ ^ n)⁻¹ = ENNReal.ofReal (R ^ n) := by
      rw [← ENNReal.inv_pow, inv_inv]
      simp [r, ENNReal.ofReal_pow (le_of_lt hR)]
    have hainv : a⁻¹ = ENNReal.ofReal w⁻¹ * ENNReal.ofReal (R ^ n) := by
      dsimp only [a]
      rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hw).ne')
        (Or.inl ENNReal.ofReal_ne_top)]
      rw [ENNReal.ofReal_inv_of_pos hw, hpow]
    calc
      a⁻¹ * ENNReal.ofReal C =
          ENNReal.ofReal (w⁻¹ * R ^ n) * ENNReal.ofReal C := by rw [hainv]; rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hw))]
      _ = ENNReal.ofReal (w⁻¹ * R ^ n * C) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by rw [hreal]
  have hmul' : a⁻¹ * (a * derivativeSup n f) ≤ a⁻¹ * ENNReal.ofReal C := by
    calc
      _ = a * derivativeSup n f * a⁻¹ := by ac_rfl
      _ ≤ ENNReal.ofReal C * a⁻¹ := hmul
      _ = a⁻¹ * ENNReal.ofReal C := by ac_rfl
  rw [hleft, hfactor] at hmul'
  exact hmul'

                                                                               
                                                          
                       
                                               
                      
                                     
                                                               
                       
                                                                            
                                                              
                                                                                  
                                       
                             
                                                           
                                                  
                                                                  
                                                               
                                                 
                              
                                                              
                                                                       
                            
               
                                                               
                                              
                                                               
      
                                                               
                                                            
                                                                                 
                         
                                                                                       
                                              

                                                                            
                                                                           
                        
                                                 
                                              
                                            
                                                      
                                       
                                                       
                                                           
                                                     
                                                        
                                                   
                                                   
                                                                                     
                                                                                      
                                       
                               
                                                                                     
                                                 
                                                                 
                                                                 
                                                 
                                      

                                                                            
                                                                             
                                               
                                          
                                              
                                            
                                                      
                                       
                                         
                                     
                              
                                                     
      
                              
                                                                   
          
                                                                   
                                                 
                                                                           
                                                   
                                                    
                                                                  

                                                                        
                                                                           
                                                                        
                                      
                                          
                                            
                                         
                                       
                                                       
                                              
                                                                            
                                       
                                                      
                                                       
                                                            
                                            
                                          
                                                 
                                                                                       
                               
                                                              
                                           
              
                                                                            
                                       
                                                                             
                   
                       
                      
      
                                                                  
                                    
                                          
                                   
                               
                                                                        
                                       
                                      

                                                                          
                 
                                               
           
                                            
                 
                        
                                                      
                                              
                                              
                                                      
                                                                                 

                                                                                  
                                              
           
      
                                      
                                                                                             
                                                               
                               

                                                                        
                                 
                                              
                                                          
                                                     
                                                                      
                                                                            
                  
         
                                
                                                                           
                                                                                    
                             
        
                                                                                     
                                                                               
                                        
                                       
                                                              
                                               
                                                                
      
                     
                                                 
                                                
                                
                                                            
                                   

                                                          
                                            
                                          
                                            
                                                    
                                        
                                            
                                                        
                                             
                                                  
                                          
                
                                    
              
                                             
                                                            
        
                                              
                                    
                                                                                
                            
                                                                             
                                                                      
              
      
                                                                                       
                                
                                                                         
                           
                                  

                                                                       
                                           
                       
                                                          
                                       
                                                                       
                                                            
                              
             
                                                                             
                                                                             
                                                         
                                                                
                                                                     
                                                      
                                                            
                                                                  
                                                                           
                      
           

                                                                    
                                                             
                                       
                                               
                         
                                                                   
                                                          
                                                                    
                
                                                                                  
                                  
                            
                                    
                                                                                     
                  
                                                                      
                                             
            
                      
           
                                                   
                                                                            
                                                             
                                                               
                                                    
                                                                         
                                  
                                        
                                                   
                           
                                                   
                                                                            
                                                            
                                                                             
                                                 
                      
                                                
                                                     
                                                                      
                     
                                        
                                                   
                                                                                      
                                                                                            
                              
                                                       
                                                       
                                                                            
                                                 
                                                           
                          
                                                                             
                                         
                                         
                                                             
                                        
                                       
                                                               
                                       
                                                                                            
                          
                                                           
                                                                  
                                                
                                                       
                                                                    
                                                                 
                                                                             
                                                       
                                     
                                                            
                                                                            
                                                                    
                                                                          
                             
                                                
                                              
                                                                 
                                        
                                                               
                                                             
                                                                 
                                         
                                                                
                                            
                                                      
                    
                                                                   
                                          
                                                          
                                           
                                   
                                                              
                                                                           
                                                                              
                                               
                                   
                                                                             
                                                                          
                                                   
                                                                           
                                         
                                     
                                                                    
                                                                                       
                          
                               
                                                            
                                                                     
                                 
                                                             
                                                                        
                                     
                    
              
                     
                                                        
                                         
                                 
                                                            
                                                                     
                                                               
                                                         
                                  
                                         
                                                                        
                          
                                                                                          
                           
                                                                                       
              
            
                        
                                                                 
                                                         
                                  
                                         
                                                                            
                                                                 
                                                              
                                                            
                                                                 
                                                                  
                      
          
                                     
                                                                  
                                        
                                        
                                                                     
                                                           
                                        
                                                                 
                                                            
                                                
                                                 
                                                       
                                                                                  
                   
                                                                   
                           
              
                                                     
                                                                       
                                  
                                        
                                                 
                           
                                                
                                              
                                                                             
                                                              
                                                         
                                          
          
                                                              
                                                         
                                                             
                                                                
                                                                         
                                     
                                                         
                  
                  
          
                                                                      
                            
                                                          
                                                                 
                                                         

end AVenhance.FaaDiBruno

end
