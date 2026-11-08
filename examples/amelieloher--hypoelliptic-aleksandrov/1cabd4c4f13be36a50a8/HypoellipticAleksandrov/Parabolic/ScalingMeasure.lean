module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure scaling for parabolic affine maps

This module proves the determinant, Haar-measure, and restricted `L^(d + 1)`
change-of-variables formulas for the affine map which multiplies time by
`r^2` and every velocity coordinate by `r`.  The results are stated for the
literal product Lebesgue measure on `TimeVelocity d`; no density-to-point or
higher-level parabolic estimate is imported here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

                                                            
                                                                        
                                                                         
                     
                         
     

                                                                      
                                             
                                                                    
                                         
                                                        
                                                               
                                                                            
                              
                     
                
         
       

                                                          
theorem parabolicAffine_injective_of_ne_zero {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : r ≠ 0) : Function.Injective (parabolicAffine t₀ v₀ r) := by
  intro z w hzw
  apply Prod.ext
  · have htime := congrArg Prod.fst hzw
    change t₀ + r ^ 2 * z.1 = t₀ + r ^ 2 * w.1 at htime
    apply mul_left_cancel₀ (pow_ne_zero 2 hr)
    linarith
  · ext i
    have hvelocity := congrFun (congrArg Prod.snd hzw) i
    change v₀ i + r * z.2 i = v₀ i + r * w.2 i at hvelocity
    apply mul_left_cancel₀ hr
    linarith

/-- A nonzero-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding_of_ne_zero {d : ℕ} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hr : r ≠ 0) :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  (contDiff_infty_parabolicAffine t₀ v₀ r).continuous.measurableEmbedding
    (parabolicAffine_injective_of_ne_zero hr)

/-- A positive-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : 0 < r) :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  parabolicAffine_measurableEmbedding_of_ne_zero hr.ne'

                                                                          
                                                                    
                               
                          
                          

                                                              
                                       
                                                                          
          
     

                                                                             
                                                 
                                                                            
                  
                                                                               
                                                     
                                                                 
                                                                           
                                                                                      
                                                   
                                                  
                
                                                                                    
                        
                      
                                                                             
                                                              
                                                            
                                       
                                                                
      
                                                                               
                                                           
                                                        
                                                                
                                                 
         
                                                                              
                  
                                                                            
                                                                  
                        
                                                             
                                                        

                                                                             
                             
                                                                         
                                                     
                                                                        
                                                   
                                    
      
                                                                        
                                                                                   
                                                                  
                                             
                                                   
                                                     
                                                                         
                                  

                                                                              
                                                     
                                                                                            
                                                             
                                            
                                                                                    
                                                      
      
                                                               
                                             
                                                                                              
                    
                                                               
                                         
                                                                   
                                            

                                                                           
                                                                        
                                                                         
                                                                              
                        
                                                           
                
                                           
                                             
                                                                   
                                                                    
                                     
                                                  
                       
                                                                     
                                                                                   
                                                          
                                     
                                            
                                                           
                                                                                 
                                                              
                                       

private theorem parabolicExponent_toReal (d : ℕ) :
    (parabolicExponent d).toReal = (d : ℝ) + 1 := by
  unfold parabolicExponent
  have hcast : (d : ℝ≥0∞) + 1 = ((d + 1 : ℕ) : ℝ≥0∞) := by
    norm_num
  rw [hcast, ENNReal.toReal_natCast]
  norm_num

                                                                            
                                                     
                                         
                                            
                                               
                            
                                                
         
           
                 
      

                                                                               
                                                                             
                                        
                                                                            
                                                                      
                       
                                                           
                                     
                                                                  
                                                           
                                            
                          
      
                         
                                                                   
                         
                                                     
                                              
                                                                              
                                                                               
                                       
                                                                              
                                                                                  
                                                                 
                                               
                                                                     

end HypoellipticAleksandrov.Parabolic
