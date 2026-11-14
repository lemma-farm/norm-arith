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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.RegularityStructures.Torus.Basic ====
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
set_option linter.unusedVariables true
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_e965b8cd37a6c1377a81_SemigroupTestDouble ====
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
set_option linter.unusedVariables true
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


/-- Fubini for a product `A(u) T(u, v)` whose inner integral is bounded by `K(u)`. -/
theorem integrable_integral_prod_mul_le {A K : SpaceTime → ℝ} {T : SpaceTime → SpaceTime → ℝ}
    (hA : Measurable A) (hA0 : ∀ u, 0 ≤ A u) (hT : Measurable fun w : SpaceTime × SpaceTime =>
      T w.1 w.2) (hT0 : ∀ u v, 0 ≤ T u v)
    (hinner : ∀ u, Integrable (T u) ∧ ∫ v, T u v ≤ K u)
    (hAK : Integrable (fun u => A u * K u)) :
    Integrable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) ∧
      ∫ w : SpaceTime × SpaceTime, A w.1 * T w.1 w.2 ≤ ∫ u, A u * K u := by
  have hFm : Measurable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) :=
    (hA.comp measurable_fst).mul hT
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ A w.1 * T w.1 w.2 := fun w =>
    mul_nonneg (hA0 _) (hT0 _ _)
  have hinn : ∀ u, ∫ v, ‖A u * T u v‖ = A u * ∫ v, T u v := by
    intro u
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact Real.norm_of_nonneg (mul_nonneg (hA0 u) (hT0 u v))
  have hint : Integrable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun u => (hinner u).1.const_mul (A u)
    · have hmeas : AEStronglyMeasurable (fun u => ∫ v, ‖A u * T u v‖) volume :=
        hFm.norm.aestronglyMeasurable.integral_prod_right'
      refine Integrable.mono' hAK hmeas (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hinn u]
      exact mul_le_mul_of_nonneg_left (hinner u).2 (hA0 u)
  refine ⟨hint, ?_⟩
  calc ∫ w : SpaceTime × SpaceTime, A w.1 * T w.1 w.2
      = ∫ u, ∫ v, A u * T u v := integral_prod _ hint
    _ ≤ ∫ u, A u * K u := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => integral_nonneg fun v => mul_nonneg (hA0 u)
            (hT0 u v)) hAK (Filter.Eventually.of_forall fun u => ?_)
        beta_reduce
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hinner u).2 (hA0 u)

namespace SemigroupTestProfile
variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

end SemigroupTestProfile
end RegularityStructures
end
