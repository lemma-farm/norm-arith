/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.KernelBoundsGlobal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsSupport
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsConvolution
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Uniform singular bound for the mollified massive heat kernel

The compact support of the periodised mollifier and the global singular majorant for the massive
heat kernel give the ε-uniform estimate for the mollified kernel.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
theorem rpow_neg_three_le_mul (x y L : ℝ) (_hx : 0 < x) (hy : 0 < y) (hL : 0 < L)
    (hxy : y ≤ L * x) :
    x ^ (-(3 : ℝ)) ≤ L ^ (3 : ℝ) * y ^ (-(3 : ℝ)) := by
  have hyL : 0 < y / L := div_pos hy hL
  have hbase : y / L ≤ x := (div_le_iff₀ hL).2 (by simpa [mul_comm] using hxy)
  have hmono := Real.rpow_le_rpow_of_nonpos hyL hbase (by norm_num : -(3 : ℝ) ≤ 0)
  have hid : (y / L) ^ (-(3 : ℝ)) =
      L ^ (3 : ℝ) * y ^ (-(3 : ℝ)) := by
    rw [Real.div_rpow hy.le hL.le, Real.rpow_neg hy.le, Real.rpow_neg hL.le]
    field_simp
  exact hmono.trans_eq hid
end Phi43
end RegularityStructures
end
