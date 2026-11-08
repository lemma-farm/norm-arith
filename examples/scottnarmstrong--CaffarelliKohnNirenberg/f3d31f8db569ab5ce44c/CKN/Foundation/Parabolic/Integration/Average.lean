-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

                                                             
                                                                
                          
          

private theorem norm_vec3_sub_le_euclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)

/-! ### Measures and cylinder Fubini -/

/-- The volume measure on `ParabolicPoint` is the product of spatial and time volume. -/
theorem volume_parabolicPoint_eq_prod :
    (volume : Measure ParabolicPoint) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) :=
  rfl

                                                                    
                                                             
                                   
                                          
                   
                                                                         
                                                                          

                                                  
theorem volume_vec3Ball_lt_top {x : Vec3} {r : ℝ} :
    volume (vec3Ball x r) < ∞ := by
  have hsub : vec3Ball x r ⊆ Metric.ball x r := by
    intro y hy
    change ‖y - x‖ < r
    exact lt_of_le_of_lt (norm_vec3_sub_le_euclideanNorm x y)
      (by
        change vec3EuclideanNorm (y - x) < r at hy
        exact hy)
  exact (measure_mono hsub).trans_lt
    (measure_ball_lt_top (μ := volume) (x := x) (r := r))

                                                                
                                                                        
                                              
                               
                                                           
                                                          

                                              
theorem volume_parabolicCylinder_lt_top {x : Vec3} {t r : ℝ} :
    volume (parabolicCylinder x t r) < ∞ := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_lt_top
    (volume_vec3Ball_lt_top (x := x) (r := r))
    ENNReal.ofReal_lt_top

                                                                                 
                                                       
                            
                                                            
                                                 
                                                                   
                                                       
        
                                                   
                                                             
                                                           
                                                               
            
                                                 
                                           
                                                                 
                 
      
                                                   
                                                           
                                                            
                                                              
                                                           
                                                                              
                                                                     
                                 
         

                                                                                         
                                                        
                               
                                                                       
                                                  
                                                                     
                                                       
        
                                                    
                                                             
                                   

                           

                                                                           
                                                                       
                          
                                                               
                                                              
                                             
                                       

                                                                   
                                                                      
                   
                             
                                                         
                            
                                            
                                    

                                                                 
                                                                      
                   
                             
                                                         
                            
                                            
                                    

                                                                                   
                                                                         
                   
                                                             
                             
                                                           

                                                             
                                                               
                   
                                                         
                           
                                       

                                                                    
                                                            
                                            
                                             
                                                 
                                                                                            
                                                                    
                                 
                                                 
                            
                                                     

                                                   
                                                             
                   
                             
                                                       
                                  
                                             
                                                               
                                   
                                                          
                                          

end CKN.Foundation.Parabolic.Integration
