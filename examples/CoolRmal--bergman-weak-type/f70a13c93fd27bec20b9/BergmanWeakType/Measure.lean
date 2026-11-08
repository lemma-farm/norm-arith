/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Normalization and support of Bergman area measures -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem area_ball (c : ℂ) (r : ℝ) : area (Metric.ball c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_ball]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top,
    mul_one]

                                         
                                                             
                                                                       
                                                                  
                              
                    
                                                                                          
            

theorem area_disk : area disk = 1 := by
  simpa [disk] using area_ball 0 1

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by simpa [diskArea] using area_disk

                                               
                                  

                                                 
                                                  

                                                                               
                                                                       

                                                                                      
                              
                                                                                  
                          
         
                                                                                           
                     
                                                     
                                                     
           
                                                                                       
                                                  
             
                        
                                                                      
                  
                                                                              
                               
                                                                     
                                                                   
                                                 
                                                                   
             
                                                               
                   
                              
                          
                           
                                            
                 
                                                                      
                  
                                                                                     
                                            
                                                                    
                                                                      
                                                       
          
                                                             
           
                                                                                   
                                                                   
                                                                      
                                                       
           
                                                                                      
                           
                     
                              
               

                                                                     
                                                                                   
                                                                              
                                                                                 
            
                                                                          
                         
                                                                         
               
                                                                                             
                                                                                 
                                                                                                 
                                                          
                                               
                                                                
                                                                             
                                                                                      
                                                                  
                                        
                                                                  
                                
                                
                                      
                                               

                                                                 
                                            
                          

                                                              
                                              
                                                                                          
            

                                                                          
                                                                          
                                   
                                         
            
                                          
                  
                                
                               
                              
                                                      
                             

                                                           
                                                                                 
                                   
                                                                                      

end BergmanWeakType
