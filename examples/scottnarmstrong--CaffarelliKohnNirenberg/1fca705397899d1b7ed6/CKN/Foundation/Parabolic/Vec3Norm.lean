-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The Euclidean norm on `Vec3` satisfies the triangle inequality. -/
theorem vec3EuclideanNorm_add_le (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- The Euclidean norm on `Vec3` is invariant under negation. -/
theorem vec3EuclideanNorm_neg (v : Vec3) :
    vec3EuclideanNorm (-v) = vec3EuclideanNorm v := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_neg, norm_neg]

                                                                              
                                               
                                                                               
      
                                                                                      
                                                                                       
                                                                                  

/-- Each component of a vector in `Vec3` is bounded in absolute value by the Euclidean norm. -/
theorem abs_apply_le_vec3EuclideanNorm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  unfold vec3EuclideanNorm
  have h := Finset.single_le_sum (fun j _hj => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsq : (v i) ^ 2 ≤ ∑ j : Fin 3, (v j) ^ 2 := by
    simpa [sq_abs] using h
  exact Real.abs_le_sqrt hsq

                                                                                                   
                                              
                                   
                  
                                                
                                                             
                       
              
                                                                                
                      
                    

/-- The Euclidean norm on `Vec3` is bounded by `√3` times the sup norm. -/
theorem vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt
      (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (∑ i : Fin 3, v i ^ 2) ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        have h := norm_le_pi_norm v i
        exact (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).2 h
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := by
    rwa [sq_le_sq] at hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

                                                                                               
                                                 
                                                  
                          
                                                                       
        
                                                             
                                                   
                     
                                        
                                    
                                           
                                           
                                           
                                   
                             
                                                                                       
      
                                                             
                            
                                          
                             
                                 

                                                                                       
                                      
                                                   
                                                                        
                       
                            
            
                                    

end CKN.Foundation.Parabolic
