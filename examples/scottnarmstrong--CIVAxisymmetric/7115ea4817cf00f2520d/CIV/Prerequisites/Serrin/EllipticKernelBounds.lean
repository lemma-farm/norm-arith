-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Harmonic.Interior
public import CKN.Foundation.Parabolic.Topology
public import CKN.Foundation.Parabolic.BallBasics
public import CKN.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CIV

/-!
# Ball integral of the Newtonian kernel gradient

The gradient `∂ₗN` of the Newtonian kernel is bounded by `(4π)⁻¹` times the Euclidean-norm
power `|z|^{-2}`, so its integral over the Euclidean ball `{y : |y - x| ≤ ρ}` is absolutely
convergent and scales linearly in `ρ`: `∫_{|y-x|≤ρ} |∂ₗN(x - y)| ≤ Cρ`. The scaling identity
`∫_{|z|≤ρ} |z|^{-2} = ρ · ∫_{|z|≤1} |z|^{-2}` is obtained from the Haar-measure scaling formula
`∫ f(c • z) dz = |c|^{-n} ∫ f(z) dz` applied to the indicator of the unit ball. This is an elliptic
kernel estimate of the interior estimates of `lem:aniso:annulus`.
-/

private theorem abs_neg_mul_rpow_nonneg (a b : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    |(-a * b * X)| = |a| * |b| * X := by
  rw [show -a * b * X = -(a * b * X) from by ring, abs_neg, abs_mul, abs_mul, abs_of_nonneg hX]

private theorem abs_spatialDeriv_newtonianKernel_le_euclidean {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |spatialDeriv newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
  rw [newtonianKernel_spatialDeriv_formula hz i]
  have hqi : q z ^ (-(3 : ℝ) / 2) = vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
    rw [q_eq_vec3Norm_sq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) from by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) from by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  rw [hqi]
  have hzpos : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hz0
    exact hz ((WithLp.toLp_eq_zero 2).mp hz0)
  have hnn3 : 0 ≤ vec3EuclideanNorm z ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg (vec3EuclideanNorm_nonneg z) _
  rw [abs_neg_mul_rpow_nonneg (4 * Real.pi)⁻¹ (z i) hnn3]
  have hcoord : |z i| ≤ vec3EuclideanNorm z := abs_apply_le_vec3EuclideanNorm z i
  have hstep : vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
      vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    have h1 : vec3EuclideanNorm z ^ (1 : ℝ) * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
        vec3EuclideanNorm z ^ ((1 : ℝ) + -(3 : ℝ)) := (Real.rpow_add hzpos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    norm_num
  calc |(4 * Real.pi)⁻¹| * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
      |(4 * Real.pi)⁻¹| * vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)) hnn3
    _ = (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
        ring
    _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by rw [hstep]

/-! ## Part 2: integrability and the scaling identity on the Euclidean ball -/

                                                                               
                                                              
                            
                                     

                                                              
                                                                        
                                                 
                                                                     

                                                                  
                                                                                     
                                                                                                    
                                                              
                                                                                                   
                                                                                           
                   
                                                                                                   
                                                                   
                                                      
                                              
            
                                                                       
                                        
                                                                    
                                                              
                                                                                       
                              

                                                                                             
                                                                   
                                                      
                                                                       
                                    
                                                                                      

                                                                     
                                                        
                                                              
               

                                                                        
                                                                                   
                                                                                             
                                                                    
                                                          
                                      
                                                            
                                                           
           
                                                                                
                                                              
                                                                                  
                                               
                                         
                                                                                 
                                                               
                                                            
                                                        
                                                                                
                                                                
                                                                
                                                          
                                                                                
                                                                          
                                                                                             
                                                               
                                                                                    
                                                                                             
                                                                      
                                              
                                                                           
                                 
                          
                                                               
                                                                                 
                                                      
                                                                                                 
                           
                                                                                         
                    
                                 
                                                                                         
              
                                                                                              
                    
                                                                     
                                         
                                                               
                                               
                    
                                                                 

                                                  

                                                                    
                                                                      
                                                      
       
                                                                    
                                                                

                                                                                   
                                                                  
                                                            
                                                                       
                                               
                                                            
                                              
                                                                                    
                                                

                                                                                   
                                                                   
                                                
                                                                            
               

                                                                                              
                                                                  
                                                  
                                                                                                 
                 
                                                                                             
               
                               
               
                                                                                                 
             
                                                         
                                                      
                
                                                                       
                                               
                                                            
                                              
                                                                                        
                                                      
                                                    
                                                             
                                                 
                                                    
                                                                    
                                                                                                
                                                 
                                                                                      
                                                                         
                                                                                        
                                                                                              
                                                                        
                                                                                    
                                                                         
                                            
                                 
                                                                                              
                                                               
                                       
                                                                            
                                                      
                                                                                         
                                                  
                                                                        
                                          
                            
                                                       
                   
                                                                                                  
                                                          
                                                                   
                                                                 
                                                                            
                                                                        
                                                                      
                                              
                                                                                            
                                                                                  
                                                                                  

end CIV
