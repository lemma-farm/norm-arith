module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.GammaShiftAmplitude
public import MathCollab.Density.Stronger.Fourth.SquareKernelFar
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem zetaGammaShiftError_le_quadratic
    {t c : ℝ} (ht : 4 ≤ t) (hc : 0 ≤ c) {w : ℂ} (u : ℝ)
    (hw : ‖w‖ ≤ c+|u|) :
    zetaGammaShiftError t w ≤ 17*c/4+c^2+u^2+17*|u|/4 := by
  have hnum : 17*‖w‖+2*‖w‖^2 ≤ 17*(c+|u|)+2*(c+|u|)^2 := by
    gcongr
  calc
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/t :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
    _ ≤ _ := by nlinarith [sq_nonneg (c-|u|), sq_abs u]

                                           
                                                 
                                                           
                                          
                                                      
                                   
                                                          
                                 
          
      
                                                         
                                                   
                               
                                                  
                                                                          
               
               
                                                
             
          

                                                                   
                               
                                   
                                            
                                      
                             
                             
                                
                                             
                                        
                     
                                 
                            
                      
                                      
                                                         
                                                    
                                                             
                                                          
                                                       
                                                                                      
                                                       
                                            
                                                  
                                                               
               
                                                  
                                                    
                                                       
                                                                
                                                  
                                                
                                                             
                                                                     
                     
                                                                
                                       
             
                                                                      
                                                            
                              
           
                 
        
                                                                        
                       
           
        
                                     
                                                                 
                              
                                                
                                                        
      
                                               
                                                           
            
                         
                                                                                   
                                                                               
               
          
                                                                                    
            
                                                                       
                       

                                                              
                               
                       
                                            
                                      
                                                                
                                                              
                               
                  
                                 
                         
                                                           
                                                         
                                                             
        
                                                     
                                    
              
                               
                                                          
                                                             

                                                      
                                               
                                                                      
                                                       
                                                                 
                                                                            
                                                                                 
                                                          

                                                                       
                             
                       
                                                       
                                          
                                                            
                  
                
                                                                 
                                                                            
      
                                            
                                                                            
                                    
                                                          


end MathCollab.Density.Stronger.Fourth
