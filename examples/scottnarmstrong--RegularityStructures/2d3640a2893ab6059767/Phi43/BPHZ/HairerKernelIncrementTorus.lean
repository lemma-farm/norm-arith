/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelIncrement
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.Torus.KernelBoundsGeometry
import RegularityStructures.PDE.SmoothDense
import Mathlib.Algebra.Order.Chebyshev

/-!
# Increment bound for the periodised Hairer kernel

For `K♯_N = hairerKernelTorus N` we prove `|K♯_N (z + h) - K♯_N z| ≲ s(h) s(z)⁻⁴` whenever
`s(h) ≤ s(z) / 2`, where `s = torusParabolicSize`.  We write both periodisations as finite sums
over the lifts `(z.1, c + k)` of `z`, where `c` is the centred representative of `z.2`; the
increment `(h.1, d)` with `d` the centred representative of `h.2` is then fed into the Euclidean
bound `hairerKernel_sub_abs_le_of_le`.  The comparison `‖(h.1, d)‖ ≤ (9/5) s(h)` between the
`ℓ¹` and `ℓ²` spatial norms is why the Euclidean bound is needed with ratio `9/10`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private noncomputable def kincBox : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2

private theorem kinc_hairerKernel_zero_of_one_lt {N : ℕ} {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : hairerKernel N z = 0 := by
  unfold hairerKernel
  have hzero : ∀ n, annShellC N n z = 0 := fun n =>
    annShellC_eq_zero (lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hz)
  rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
  simp

/-- A lift `y` of `z.2` with coordinates in `[-1, 1]` computes the periodisation as a finite sum. -/
private theorem kinc_torus_eq_sum (N : ℕ) (z : SpaceTime) {y : Fin 3 → ℝ}
    (hy : RegularityStructures.torusProj y = z.2) (hy1 : ∀ i, |y i| ≤ 1) :
    hairerKernelTorus N z =
      ∑ k ∈ kincBox, hairerKernel N (z.1, y + fun i => (k i : ℝ)) := by
  have hab : RegularityStructures.torusProj (torusRep z.2) = RegularityStructures.torusProj y := by
    rw [hy]; exact RegularityStructures.PDE.torusProj_torusRep z.2
  choose m hm using fun i => RegularityStructures.PDE.exists_int_of_torusProj_eq hab i
  let g : (Fin 3 → ℤ) → ℝ := fun k => hairerKernel N (z.1, y + fun i => (k i : ℝ))
  have hshift : hairerKernelTorus N z = ∑' k, g k := by
    unfold hairerKernelTorus
    rw [← (Equiv.subRight m).tsum_eq g]
    refine tsum_congr fun k => ?_
    simp only [g, Equiv.subRight_apply]
    congr 2
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_sub, hm i]
    ring
  rw [hshift]
  refine tsum_eq_sum fun k hk => ?_
  by_contra hne
  apply hk
  have hnorm : parabolicNorm (z.1, y + fun i => (k i : ℝ)) ≤ 1 := by
    by_contra h
    exact hne (kinc_hairerKernel_zero_of_one_lt (lt_of_not_ge h))
  unfold kincBox
  rw [Fintype.mem_piFinset]
  intro i
  have hi : |y i + (k i : ℝ)| ≤ 1 := by
    have h1 : |y i + (k i : ℝ)| ≤ ∑ j, |y j + (k j : ℝ)| :=
      Finset.single_le_sum (f := fun j => |y j + (k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    unfold parabolicNorm at hnorm
    simp only [Pi.add_apply] at hnorm
    linarith [Real.sqrt_nonneg |z.1|]
  have hlo := (abs_le.1 hi).1
  have hhi := (abs_le.1 hi).2
  have hyi := abs_le.1 (hy1 i)
  rw [Finset.mem_Icc]
  constructor
  · have : (-2 : ℝ) ≤ k i := by linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ 2 := by linarith
    exact_mod_cast this

/-- The centred representative is the shortest lift. -/
private theorem kinc_spatialNorm_le_l1 (x : Torus3) {y : Fin 3 → ℝ}
    (hy : ∀ i, ∃ n : ℤ, y i = torusCenteredRep x i + n) :
    torusSpatialNorm x ≤ ∑ i, |y i| := by
  have hc : ∀ i, |torusCenteredRep x i| ≤ |y i| := by
    intro i
    obtain ⟨n, hn⟩ := hy i
    have := sq_centered_add_int_ge (torusCenteredRep_mem_Icc x i) n
    rw [← hn] at this
    exact sq_le_sq.1 this
  have hsum0 : 0 ≤ ∑ i, |y i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold torusSpatialNorm
  rw [Real.sqrt_le_left hsum0]
  unfold sqNorm3
  calc ∑ i, torusCenteredRep x i ^ 2 = ∑ i, |torusCenteredRep x i| ^ 2 := by simp only [sq_abs]
    _ ≤ (∑ i, |torusCenteredRep x i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ (∑ i, |y i|) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _)
          (Finset.sum_le_sum fun i _ => hc i) 2

                                                                                              
                                         
                                                                  
                                      
                                   
                                                                                          
                                                                                               
                    
                                                                            
                                                
                  
                                                                                      
                                                    
                                              
                                                                       
                                                                                         
                       

                                                                                         
                 
                                              
                                                                    
                                                       
                                                               
                                                                            
                                                         
                                                         
                 
                                       
                                       
                                        
           
                                                                      
                                                          
                                                                      
                                                          
                                                                                                 
                                       
                                                               
                                                       
                                         
                                                                                    
                                                
                                                                   
                                                        
                                                               
                                             
           
                          
            
                                          
        
                                   
                                                                    
                                                                                            
                                                                        
                                           
                          
             
                                      
                                                                                
                                                                              
           
                                                                                   
                                             
                                                                      
                                      
                                        
              
                                        
                             
                                                                  
                                                       
                                                                                   
             
                              
                                                                         
                                                 
                                                                        
                                            
                                                      
                                                                  
                                          
                                                                        
                                                                                       
                                                                                      
                                           
                                                                                 
                                                     
                                                            
                                                                    
                                    
                      
                                       
                                                                                   
                                                      
                                                                                   
                                                           
                                                                         
                                                                     
                                                         
                                                                                                
                               
                                                         

end RegularityStructures.Phi43

end
