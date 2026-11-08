module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicAbelPhase
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open Finset MeasureTheory
open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle CookMagyarArcs CookMagyarFiniteFourier

private theorem cubicAbelWeight_deriv_bound_Icc (beta : ℝ) (N : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) N) :
    ‖deriv (cubicAbelWeight beta) t‖ ≤
      2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1) := by
  have ht2 : t ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hpoly : |3 * t ^ 2 - 1| ≤ 3 * (N : ℝ) ^ 2 + 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg t]
  have hcoeff : 0 ≤ 2 * Real.pi * |beta| := by positivity
  rw [cubicAbelWeight_deriv_norm, abs_mul, abs_mul]
  calc
    |2 * Real.pi| * |beta| * |3 * t ^ 2 - 1| =
        (2 * Real.pi * |beta|) * |3 * t ^ 2 - 1| := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    _ ≤ (2 * Real.pi * |beta|) * (3 * (N : ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hpoly hcoeff

private theorem norm_cubicAbelWeight_sub_integral_unit_le
    (beta : ℝ) (N k : ℕ) (hk : k < N) :
    ‖cubicAbelWeight beta k -
        ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta t‖ ≤
      2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1) := by
  let B : ℝ := 2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfint : IntervalIntegrable (cubicAbelWeight beta) volume
      (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    (cubicAbelWeight_differentiable beta).continuous.intervalIntegrable _ _
  have hconst :
      (∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta k) =
        cubicAbelWeight beta k := by
    simp
  rw [← hconst, ← intervalIntegral.integral_sub
    (intervalIntegrable_const) hfint]
  have hpoint : ∀ t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ),
      ‖cubicAbelWeight beta k - cubicAbelWeight beta t‖ ≤ B := by
    intro t ht
    have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    rw [Set.uIoc_of_le hkle] at ht
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    have hsuccN : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
    have htIcc : t ∈ Set.Icc (0 : ℝ) N :=
      ⟨(Nat.cast_nonneg k).trans ht.1.le, ht.2.trans hsuccN⟩
    have hkIcc : (k : ℝ) ∈ Set.Icc (0 : ℝ) N :=
      ⟨by positivity, hkN⟩
    have hLip := (convex_Icc (0 : ℝ) (N : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _hx => (cubicAbelWeight_differentiable beta).differentiableAt)
      (fun x hx => cubicAbelWeight_deriv_bound_Icc beta N hx)
      hkIcc htIcc
    have hdist : ‖t - (k : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
      rw [this] at ht
      linarith [ht.2]
    calc
      ‖cubicAbelWeight beta k - cubicAbelWeight beta t‖ =
          ‖cubicAbelWeight beta t - cubicAbelWeight beta k‖ := norm_sub_rev _ _
      _ ≤ B * ‖t - (k : ℝ)‖ := hLip
      _ ≤ B := by nlinarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlength : |((k + 1 : ℕ) : ℝ) - (k : ℝ)| = 1 := by
    norm_num
  simpa [B, hlength] using hnorm

/-- Comparing the phase sampled at the integers with its real integral
costs at most one endpoint and one derivative bound per unit interval. -/
theorem norm_sum_cubicAbelWeight_sub_integral_le (beta : ℝ) (N : ℕ) :
    ‖(∑ k ∈ Icc 0 N, cubicAbelWeight beta k) -
        ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t‖ ≤
      1 + (N : ℝ) *
        (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
  have hsum : (∑ k ∈ Icc 0 N, cubicAbelWeight beta k) =
      (∑ k ∈ Finset.range N, cubicAbelWeight beta k) +
        cubicAbelWeight beta N := by
    rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ]
  have hint :
      (∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t) =
        ∑ k ∈ Finset.range N,
          ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta t := by
    have hpart := intervalIntegral.sum_integral_adjacent_intervals
      (f := cubicAbelWeight beta) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := N)
      (fun k _hk =>
        (cubicAbelWeight_differentiable beta).continuous.intervalIntegrable
          (k : ℝ) ((k + 1 : ℕ) : ℝ))
    calc
      (∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t) =
          ∫ t in (0 : ℝ)..(N : ℝ), cubicAbelWeight beta t := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N),
          ← integral_Icc_eq_integral_Ioc]
      _ = ∑ k ∈ Finset.range N,
          ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta t := by
        simpa using hpart.symm
  calc
    ‖(∑ k ∈ Icc 0 N, cubicAbelWeight beta k) -
        ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t‖ =
      ‖(∑ k ∈ Finset.range N,
          (cubicAbelWeight beta k -
            ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta t)) +
        cubicAbelWeight beta N‖ := by
      rw [hsum, hint, Finset.sum_sub_distrib]
      abel_nf
      simp only [add_comm (1 : ℕ)]
    _ ≤ (∑ k ∈ Finset.range N,
          ‖cubicAbelWeight beta k -
            ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), cubicAbelWeight beta t‖) +
        ‖cubicAbelWeight beta N‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_sum_le _ _) (le_refl _))
    _ ≤ (∑ _k ∈ Finset.range N,
          2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) + 1 := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        exact norm_cubicAbelWeight_sub_integral_unit_le beta N k
          (Finset.mem_range.mp hk)
      · rw [cubicAbelWeight_norm]
    _ = 1 + (N : ℝ) *
        (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
      simp [add_comm]

/-! # Abel summation in one cubic residue class

The residue-class sum is rewritten as an ordinary natural-number sum.  This
isolates the arithmetic progression discrepancy needed for the major-arc
estimate, without assuming that discrepancy is already known.
-/

                                                                  
                                         
                                                  
                                                                        

                                       
                                                        
                                     
                    
                                                                         
           
                                               
                        
                                      
                                                        
                                                          
                                                                 
                                       
                                                    
                                         
                                                          
                                                                      
                                                   
                                                               
                               
                                                  
                                               
                                   
           
                                  
                                 
                            
               
                                                                       
                                
                                                     
                                           

                                                                   
                                                                       
                                                             
                                              
                                                          
                                                           

                                                         
                                        
                                                  
                                              

                                                               
                                                     
                                                           
                                    
                                                       
                                                             
                                                  

                                                       
                                                                
                   
                                                                             
                                       
                          
                                                                
              
                     
                                                                    
                        
                                                              
                          
                           
                                                               
          
                                 
                                                 
                                                                       

                                                                         
                                                                           
                                                   
                                                  
                                           
                                  
                                     
                                   
                                                                         
                                      
                          
                                                             
                            
                                                             
                                                        
                                                      
                                                             

                                                                      
                                                                           
                                                                          
                                                        
                                           
                                  
                                     
                   
                                     
                                                             
                                      
                          
                                                             
                            
                                                             
                                                                         
            
                                                              
                          
                                                    
                   

                                                                    
                                                                          
                                                          
                                      
                                  
                                     
                                 
                                     
                                                             
                                                           
                                              
                                                             
               
                               
                                                                
                                                            
                                                             
                       
                            
                                                        
                                                              
                                     
                           

end CookMagyarMajorArc
end SystolicGrowth
