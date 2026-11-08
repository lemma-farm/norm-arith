/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
Modified for enaslund/unit-distance-bound: import lines relocated from
DedekindResidue.* to UnitDistance.Upstream.AINTLIB.* and `public import Mathlib`
narrowed to specific Mathlib modules for the Lean 4.32.0 / Mathlib 81a5d257 pin;
proof text unchanged. Upstream and local hashes: third-party/aintlib/manifest.json.
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Tactic
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.ThetaEstimates

/-!
# The abstract functional-equation pair of the total Hecke theta  (SP1-AGE-4, brick 4c)

Everything before this file culminates in one object: **`heckeFEPair : WeakFEPair ℂ`** —
the total normalised theta `f(x) = ∑_C Ĝ_C(x)` together with

* its clean symmetry `f(1/x) = x^{1/2}·f(x)` (`heckeF_inversion`, so weight `k = 1/2` and
  root number `ε = 1`),
* local integrability on `(0,∞)` (from `continuousOn_heckeF`),
* and super-polynomial approach to the constant term `f₀ = h·w⁻¹·vol`
  (`heckeF_sub_const_isBigO`, from the exponential deviation bound and
  `isBigO_exp_neg_rpow`).

Mathlib's abstract Mellin machinery (`Mathlib.NumberTheory.LSeries.AbstractFuncEq` — the
engine underneath `completedRiemannZeta`) now provides, for free: an entire `Λ₀`, the
meromorphic `Λ` with poles exactly at `σ ∈ {0, 1/2}` and known residues, the Mellin
representation on `Re σ > 1/2`, and the functional equation `Λ(1/2 − σ) = Λ(σ)`.
`Λ_K(s)` will be `heckeFEPair.Λ (s/2)` up to an explicit constant adjustment.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open Asymptotics Filter
open scoped nonZeroDivisors Real


/-- A stretched-exponential `exp(-c·x^p)` beats every power at infinity. -/
theorem isBigO_exp_neg_rpow {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (r : ℝ) :
    (fun x : ℝ => Real.exp (-c * x ^ p)) =O[atTop] fun x : ℝ => x ^ r := by
  have h1 : (fun y : ℝ => y ^ (-r / p)) =O[atTop] (fun y => Real.exp (c * y)) :=
    (isLittleO_rpow_exp_pos_mul_atTop (-r / p) hc).isBigO
  obtain ⟨C, hC⟩ := h1.bound
  have htend : Filter.Tendsto (fun x : ℝ => x ^ p) atTop atTop := tendsto_rpow_atTop hp
  have hev := htend.eventually hC
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop (1:ℝ)] with x hx h1x
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos h1x
  have hxr_pos : (0:ℝ) < x ^ r := Real.rpow_pos_of_pos hx0 _
  have hexp_pos : (0:ℝ) < Real.exp (c * x ^ p) := Real.exp_pos _
  have hxp : (x ^ p) ^ (-r / p) = x ^ (-r) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hx ⊢
  rw [hxp, Real.rpow_neg hx0.le, abs_of_pos (by positivity), abs_of_pos hexp_pos] at hx
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hxr_pos]
  have h2 : 1 ≤ C * Real.exp (c * x ^ p) * x ^ r := by
    have h3 := mul_le_mul_of_nonneg_right hx hxr_pos.le
    rwa [inv_mul_cancel₀ hxr_pos.ne'] at h3
  have h4 : Real.exp (-c * x ^ p) = (Real.exp (c * x ^ p))⁻¹ := by
    rw [show -c * x ^ p = -(c * x ^ p) by ring, Real.exp_neg]
  rw [h4]
  calc (Real.exp (c * x ^ p))⁻¹ = (Real.exp (c * x ^ p))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (Real.exp (c * x ^ p))⁻¹ * (C * Real.exp (c * x ^ p) * x ^ r) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * x ^ r := by field_simp

                                              

                        
                                                         
                                                        
                                            
                            
                                                       
                                                              
                                                         
                                                                             
                                              
                                                          
            
                            
                                       

                        
                                                                           
                                                                            
                                                                          

                        
                                                             
                                                                  
                                                                 
                                                                          
                                                                             
                                            
                            
                                                                            
                                  
                                                                                          
                                                                        
                                                                                    
                                      
                                                       
                                                    
                                
                                                        
                                                         
                                                      
                        
                                                        
                                                                                      
                              
                                                                          
             
                                                                                
                                                                                 
                                                                   
                                                       
                 
               

                        
                                                                         
                                    
                                                                                 

                        
                                 
                                                                  
                                  
                                                                          
                                                                  
                                    
                                                                                       
                                                                     
                                          
                                                   
                                                                                         
                         
                                                                                  
                                                    
                                                              
                                   
                                         
                               
                                                                         
                                                                                    
       
            
                               
                                                                    
                               
                                                                      
                                     
                               
                                                  
                                                       
                                                
                                                                               
                              
                                                                            
                                                                                       
                 
                                                         
                                                       
                           

                        
                                                                                       
                                         
                                                                                
                                                                       
                                                                                          
                                                       
                 
                 
                                                          
                                                                      
               

                        
                                                                                        
                                                                                    
                                                                                     
                                                          
                                                  
                                
                                
            
        
                           
                           
                                                        
                                                                  
                                                        
                                                                  
                   
                   
                         
                                                    
                               
                                           
                                
             
        
                       
                                             
                              
                           
                  
                                 
                                                 
                                                                           
                                                             
                           
                       
                                             
                              
                           
                  
                                 
                                                 
                                                                           
                                                             
                           

end

end DedekindResidue
