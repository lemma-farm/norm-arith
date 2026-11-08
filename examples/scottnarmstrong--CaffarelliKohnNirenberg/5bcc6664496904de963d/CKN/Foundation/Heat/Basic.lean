-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The three-dimensional heat kernel

This file fixes the Gaussian normalization used by the parabolic estimates.
The spatial variable is the repository's `Fin 3 → ℝ` type, and the spatial
quadratic form is written as a finite sum so that it is independent of the
ambient sup norm on the function space.
-/

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! ### Definitions and elementary identities -/

def heatKernel (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, x i ^ 2) / (4 * t))
  else 0

                                              
                                           

                                    
                                   

lemma vec3EuclideanNorm_sq (x : Vec3) :
    (vec3EuclideanNorm x) ^ 2 = ∑ i, x i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (x i))

                                                                    
                            
                                  

lemma heatKernel_eq_formula {x : Vec3} {t : ℝ} (ht : 0 < t) :
  heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t)) := by
  rw [heatKernel, ite_eq_left ht, vec3EuclideanNorm_sq]

lemma heatKernel_eq_formula_sum {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) := by
  rw [heatKernel_eq_formula ht, vec3EuclideanNorm_sq]

                                                                     
                     
                                 
                                                         
                         
                                                       

                                                      
                            
                               
                                                                         

                                                         
                                               
                       
                             
                                                       
                             


                                                                        
                                   
                                      

private lemma gaussian_sum_exp_eq_prod (x : Vec3) (t : ℝ) :
    Real.exp (-(∑ i, x i ^ 2) / (4 * t)) =
      ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2) := by
  rw [show -(∑ i, x i ^ 2) / (4 * t) =
      ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) by
    calc
      -(∑ i, x i ^ 2) / (4 * t) =
          (-1 / (4 * t)) * (∑ i, x i ^ 2) := by
            field_simp
      _ = ∑ i, (-1 / (4 * t)) * (x i) ^ 2 := by rw [Finset.mul_sum]
      _ = ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) := by ring_nf]
  exact Real.exp_sum Finset.univ (fun i => -(1 / (4 * t)) * (x i) ^ 2)

private lemma gaussian_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * t))) volume := by
  rw [show volume = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) by
    exact volume_pi]
  have hprod : Integrable
      (fun x : Vec3 => ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2))
      (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) := by
    exact Integrable.fintype_prod (ι := Fin 3) (E := ℝ)
      (μ := fun _ : Fin 3 => (volume : Measure ℝ)) (fun _hi => by
      convert integrable_exp_neg_mul_sq
        (by positivity : 0 < (1 / (4 * t) : ℝ)) using 1)
  exact hprod.congr (Filter.Eventually.of_forall fun x =>
    (gaussian_sum_exp_eq_prod x t).symm)

lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernel x t) volume := by
  rw [show (fun x : Vec3 => heatKernel x t) = fun x : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) by
    funext x
    exact heatKernel_eq_formula_sum ht]
  exact (gaussian_integrable t ht).const_mul _

                                              
                                                      
                                                   
                                                                         
                    
                                                                      
                                                                        
            
                                      
                                             
                                                
                                                                     
           
                                                                  
                                                            
                                                                
                
                                                
                                      
         
                     

                                                
                                        
                                                             
                                          
                                               
            
                                       
                                                 
                                                   
                                             
                             
                                                                       
           
                            
                                                                         

                                                                             
                                   
                             

end CKN.Foundation.Heat
