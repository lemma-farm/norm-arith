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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.Phi43.BPHZ.SingularConvolutionWeights ====
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
# Integrals of parabolic power weights

For a real exponent `p`, the weights `s(z)^(-p)` restricted to the ball `s ≤ a`
(`singularLocalWeight`) or to the exterior `s > e` (`singularTailWeight`) have integrals
of order `a^(5-p)` (for `p < 5`) and `e^(5-p)` (for `p > 5`) on space-time, the homogeneous
dimension being five.  The proofs use the layer-cake formula and the global ball-volume bound.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- The power weight `s(z)^(-p)` restricted to the punctured ball `0 < s(z) ≤ a`. -/
def singularLocalWeight (p a : ℝ) (z : SpaceTime) : ℝ :=
  if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ a then
    torusParabolicSize z ^ (-p) else 0
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_1b40c1ff6c2420cd732a_TreeI3Psi2RenormHolder ====
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
# The renormalised convolution with Hölder increments

A variant of [Hai14, Lemma 10.16 (ii)] (`abs_integral_mul_sub_le`) in which the increment bound of
`f₂` is Hölder of exponent `lam ∈ (0, 1]`:
`|f₂(u + h) - f₂ u| ≤ B₂ s(h)^lam s(u)^(-a₂-lam)` for `s h ≤ s u / 2`.  If `f₁` has order `-a₁` with
`5 < a₁ < 5 + lam` and `f₂` order `-a₂`, then
`|∫ f₁(x) (f₂(z - x) - f₂ z) dx| ≤ C B₁ B₂ s(z)^(5-a₁-a₂)`.  This is needed for the difference of
renormalised convolutions, where `f₂` is a difference of kernels whose Hölder increments gain a
power of the distance between the scales by interpolation.
-/
public section
open MeasureTheory Set
namespace RegularityStructures

set_option linter.unusedVariables false in
theorem integral_renorm_majorant_near_holder {a₁ a₂ lam : ℝ} (hlam1 : lam ≤ 1)
    (ha₁ : 5 < a₁) (ha₁' : a₁ - lam < 5) 
    (h_RegularityStructures_integrable_singularLocalWeight : ∀ {p a : ℝ},
      0 < p →
        p < 5 →
          0 < a →
            MeasureTheory.Integrable (RegularityStructures.singularLocalWeight p a)
              MeasureTheory.MeasureSpace.volume)
    (h_RegularityStructures_rpow_mul_rpow_div_holder : ∀ {ρ k : ℝ}, 0 < ρ → 0 < k → ∀ (α β γ : ℝ), α + β = γ → ρ ^ α * (ρ / k) ^ β = k ^ (-β) * ρ ^ γ)
    (h_RegularityStructures_integral_singularLocalWeight_le : ∀ {p a : ℝ},
      0 < p →
        p < 5 →
          0 < a →
            ∫ (z : RegularityStructures.SpaceTime), RegularityStructures.singularLocalWeight p a z ≤
              80 / (5 - p) * a ^ (5 - p))
    :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ B : ℝ}, 0 < ρ → 0 ≤ B →
      Integrable (fun x => B * (2 ^ lam * ρ ^ (-a₂ - lam)) *
        singularLocalWeight (a₁ - lam) (ρ / 4) x) ∧
      ∫ x, B * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * K * ρ ^ (5 - a₁ - a₂) := by
  have hp : 0 < a₁ - lam := by linarith
  have h5 : 0 < 5 - (a₁ - lam) := by linarith
  refine ⟨2 ^ lam * (80 / (5 - (a₁ - lam)) * 4 ^ (-(5 - (a₁ - lam)))), by positivity, ?_⟩
  intro ρ B hρ hB
  have iL := h_RegularityStructures_integrable_singularLocalWeight hp ha₁' (by positivity : 0 < ρ / 4)
  refine ⟨iL.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := h_RegularityStructures_integral_singularLocalWeight_le hp ha₁' (by positivity : 0 < ρ / 4)
  have hc : 0 ≤ B * (2 ^ lam * ρ ^ (-a₂ - lam)) := by
    have := Real.rpow_nonneg hρ.le (-a₂ - lam)
    have h2 : (0 : ℝ) ≤ 2 ^ lam := Real.rpow_nonneg (by norm_num) _
    positivity
  have key := h_RegularityStructures_rpow_mul_rpow_div_holder hρ (by norm_num : (0 : ℝ) < 4) (-a₂ - lam)
    (5 - (a₁ - lam)) (5 - a₁ - a₂) (by ring)
  calc
    B * (2 ^ lam * ρ ^ (-a₂ - lam)) * ∫ x, singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * (2 ^ lam * ρ ^ (-a₂ - lam)) * (80 / (5 - (a₁ - lam)) * (ρ / 4) ^ (5 - (a₁ - lam))) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = B * 2 ^ lam * (80 / (5 - (a₁ - lam))) *
        (ρ ^ (-a₂ - lam) * (ρ / 4) ^ (5 - (a₁ - lam))) := by ring
    _ = _ := by rw [key]; ring
end RegularityStructures
end
