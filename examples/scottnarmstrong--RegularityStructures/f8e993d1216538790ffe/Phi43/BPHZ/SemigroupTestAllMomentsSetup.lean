/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeAllMomentsSetup
public import Phi43.BPHZ.SemigroupTestMoment

/-!
# Hypotheses of the all-moments theorem for the periodised semigroup test

The periodised semigroup kernel `q^♯_t(z, ·)` is measurable and integrable on `ℝ × T³` for every
`t > 0` (`semigroupPeriodised_chaos_data`), and has no compact support. The kernel increment
`K(y - w) - K(x - w)` of the `I`-trees is supported, for `y` in a time slab, in a fixed compact set
(`hairerI2Psi2Kernel_slab_support`). These are the inputs of
`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

                                                                    
                                                                                  
                                                                                     
                                               
                 
                                                                              
                                          
                                                                          

/-- For `y` in a time slab, the kernel increment `K(y - w) - K(x - w)` is supported in a fixed
compact set. -/
theorem hairerI2Psi2Kernel_slab_support (N : ℕ) (x : SpaceTime) (c R : ℝ) :
    ∃ S : Set SpaceTime, IsCompact S ∧
      ∀ y : SpaceTime, |y.1 - c| ≤ R → ∀ w, hairerI2Psi2Kernel N x y w ≠ 0 → w ∈ S := by
  obtain ⟨S, hSc, -, -, hS⟩ := hairerI2Psi2Kernel_chaos_support N x (c, 0) (Real.sqrt (max R 0))
  refine ⟨S, hSc, fun y hy w hw => hS y ?_ w hw⟩
  rw [Real.sq_sqrt (le_max_right _ _)]
  exact hy.trans (le_max_left _ _)

end RegularityStructures.Phi43

end
