module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.RegularityStructures.Torus.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The three-torus and space-time

We write `T³ = ℝ³/ℤ³` as `UnitAddTorus (Fin 3)` and space-time `ℝ × T³` as a product. Points of
`ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean square norm written out by hand. A function on
the torus is smooth if its periodic lift to `ℝ³` is smooth.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)
/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3

/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)
/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.RegularityStructures.Torus.KernelBoundsBasic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Parabolic size on space-time over `T³`

The singular estimates for the massive heat kernel use the parabolic size
`|z|_s = |t|^(1/2) + |x|`, with the spatial point represented in the centred fundamental cube
`[-1/2,1/2)^3`.  The representative is defined here rather than changing the existing `[0,1)`
representative used by `heatKernel`.

Sources: [Hai14] = arXiv:1303.5113v4, §2 and Assumption 5.1; [Hos25] = arXiv:2310.07396v2, §2.1.
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
/-- The centred representative of a point of `T³`, in `[-1/2,1/2)³`. -/
def torusCenteredRep (x : Torus3) : Fin 3 → ℝ := fun i =>
  if (1 / 2 : ℝ) ≤ torusRep x i then torusRep x i - 1 else torusRep x i
/-- The Euclidean spatial norm of the centred representative. -/
def torusSpatialNorm (x : Torus3) : ℝ := √(sqNorm3 (torusCenteredRep x))
/-- The parabolic size of a space-time point. -/
def torusParabolicSize (z : SpaceTime) : ℝ :=
  √|z.1| + torusSpatialNorm z.2

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_2951f275248c00a3a241_SemigroupTestDouble ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chaos-reduction double integral for a semigroup test profile

For a semigroup test profile `g` at scale `lam` and base point `x` (see `SemigroupTestProfile`) and
real exponents `ζ, e > -5`,
`∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e ≤ C lam^(ζ+e)`
(`SemigroupTestProfile.integral_double_le`).  This is the analogue of
`chaosReduction_integral_left` with the compactly supported test function replaced by a profile
with unbounded support, for which only a sup bound and moment bounds are available.

* For `e < 0` the inner integral over `v` is bounded uniformly in `u` by
  `SemigroupTestProfile.integral_mul_rpow_sub_le`.
* For `e ≥ 0` we use `s(u - v)^e ≤ 16^e (s(u - x)^e + s(v - x)^e)` and the moment bounds.
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
set_option linter.unusedVariables false in
theorem torusParabolicSize_sub_rpow_le {e : ℝ} (he : 0 ≤ e) (u v x : SpaceTime) 
    (h_RegularityStructures_torusParabolicSize_nonneg : ∀ (z : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.torusParabolicSize z)
    (h_RegularityStructures_torusParabolicSize_sub_le_eight_mul : ∀ (z w : RegularityStructures.SpaceTime),
      RegularityStructures.torusParabolicSize (z - w) ≤
        8 * (RegularityStructures.torusParabolicSize z + RegularityStructures.torusParabolicSize w))
    :
    torusParabolicSize (u - v) ^ e ≤
      16 ^ e * (torusParabolicSize (u - x) ^ e + torusParabolicSize (v - x) ^ e) := by
  have h8 := h_RegularityStructures_torusParabolicSize_sub_le_eight_mul (u - x) (v - x)
  rw [sub_sub_sub_cancel_right] at h8
  set a := torusParabolicSize (u - x) with ha
  set b := torusParabolicSize (v - x) with hb
  have ha0 : 0 ≤ a := h_RegularityStructures_torusParabolicSize_nonneg _
  have hb0 : 0 ≤ b := h_RegularityStructures_torusParabolicSize_nonneg _
  have hsum : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hmax : max a b ^ e ≤ a ^ e + b ^ e := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg ha0 _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hb0 _)
  have hle : torusParabolicSize (u - v) ≤ 16 * max a b := by
    have := le_max_left a b
    linarith
  calc torusParabolicSize (u - v) ^ e ≤ (16 * max a b) ^ e :=
        Real.rpow_le_rpow (h_RegularityStructures_torusParabolicSize_nonneg _) hle he
    _ = 16 ^ e * max a b ^ e := Real.mul_rpow (by norm_num) (le_max_of_le_left ha0)
    _ ≤ 16 ^ e * (a ^ e + b ^ e) :=
        mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)
namespace SemigroupTestProfile
variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}
end SemigroupTestProfile
end RegularityStructures
end
