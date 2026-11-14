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
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Algebra.Order.Archimedean.Basic

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.Basic ====
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

/-- The projection `ℝ³ → T³`. -/
def torusProj (y : Fin 3 → ℝ) : Torus3 := fun i => ((y i : ℝ) : UnitAddCircle)

/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HeatKernel ====
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
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) * exp (-sqNorm3 y / (4 * t))
def heatSemigroup (s : ℝ) (f : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  ∫ y : Fin 3 → ℝ, gaussKernel s y * f (x - torusProj y)
end RegularityStructures
end
/-! ### The Gaussian density on `ℝ³` -/
public section
open MeasureTheory Real
namespace RegularityStructures

/-! ### The heat semigroup -/

/-! ### Values for nonpositive times

The statement defines `γ_t`, `p_t` and `P_t` only for `t > 0`. The Lean functions are total. For
`t ≤ 0` they are zero, because `(4πt)^{-3/2}` is `0` at `t = 0` and is `exp(…) cos(-3π/2) = 0` for
`t < 0`. No result uses these values. -/

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HolderBesov ====
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
# Hölder–Besov spaces of negative order on the three-torus

For `η < 0` and `f ∈ C(T³)`,
`‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_{x ∈ T³} |P_s f(x)|` (the statement, Definition 2.1 and
equation (2.3)), and `𝒞^η` is the completion of `C(T³)` for this norm.

`holderBesovENorm` is the extended-real supremum. For `η ≤ 0` it is bounded by the supremum
norm, so it is finite, and it is subadditive because `P_s` is linear. Hence it defines an additive
group seminorm on `C(T³)`. `HolderBesov η` is the completion of `C(T³)` for that seminorm, and
`toHolderBesov η` embeds `C(T³)` into it.

Source: the statement, Definition 2.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures

/-- `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_x |P_s f(x)|`, as an extended real. -/
def holderBesovENorm (η : ℝ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ s ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ
end RegularityStructures
end
public section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures

end RegularityStructures
end
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures

end RegularityStructures
end
public section
namespace RegularityStructures
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_e5ecc48c10b59823c323_KolmogorovHolderBesovCriterion ====
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
# The dyadic Kolmogorov reduction for the negative-order torus norm

The dyadic reduction is the deterministic part of the Kolmogorov argument.  It uses the
semigroup contraction on `C(T³)` and the scale decomposition of `(0, 1]`; compare Hairer
[Hai14, (2.1)--(2.3)].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures

/-- The dyadic scale `2⁻ⁿ`, written with natural powers to avoid logarithms. -/
def dyadicScale (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n


set_option linter.unusedVariables false in
theorem holderBesovENorm_le_dyadic_iSup {η : ℝ} (hη : η ≤ 0)
    (f : C(Torus3, ℝ)) 
    (h_RegularityStructures_dyadicScale_pos : ∀ (n : ℕ), 0 < RegularityStructures.dyadicScale n)
    (h_RegularityStructures_heatSemigroup_sup_le : ∀ {r s : ℝ},
      0 < r →
        r ≤ s →
          ∀ (f : C(RegularityStructures.Torus3, ℝ)),
            ⨆ (x : RegularityStructures.Torus3), ‖RegularityStructures.heatSemigroup s f x‖ₑ ≤
              ⨆ (x : RegularityStructures.Torus3), ‖RegularityStructures.heatSemigroup r f x‖ₑ)
    (h_RegularityStructures_exists_mem_dyadicBlock : ∀ {s : ℝ},
      0 < s →
        s ≤ 1 →
          ∃ (n : ℕ),
            s ∈ Set.Ioc (RegularityStructures.dyadicScale (n + 1)) (RegularityStructures.dyadicScale n))
    :
    holderBesovENorm η f ≤
      ⨆ n : ℕ,
        ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
  refine iSup₂_le fun s hs => ?_
  obtain ⟨n, hn⟩ := h_RegularityStructures_exists_mem_dyadicBlock hs.1 hs.2
  have hβ : 0 ≤ -η / 2 := by linarith
  have hweight : s ^ (-η / 2) ≤ (dyadicScale n) ^ (-η / 2) := by
    exact Real.rpow_le_rpow hs.1.le hn.2 hβ
  have hsup := h_RegularityStructures_heatSemigroup_sup_le
    (h_RegularityStructures_dyadicScale_pos (n + 1)) hn.1.le (f := f)
  calc
    ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x : Torus3, ‖heatSemigroup s f x‖ₑ ≤
        ENNReal.ofReal (s ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
      gcongr
    _ ≤ ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
      gcongr
    _ ≤ ⨆ n : ℕ,
        ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ :=
      le_iSup (fun n : ℕ => ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
        ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ) n
end RegularityStructures
end
