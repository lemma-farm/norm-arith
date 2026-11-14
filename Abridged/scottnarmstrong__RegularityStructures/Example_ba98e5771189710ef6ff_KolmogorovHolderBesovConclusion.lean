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
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.HeatKernel ====
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

/-- The heat semigroup on `T³`: `(P_s f)(x) = ∫_{ℝ³} γ_s(y) f(x - y) dy`, where `γ_s` is the
heat kernel on `ℝ³` and `x - y` is taken in `T³`. -/
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.HeatKernelRegularity ====
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
# Uniform Gaussian bounds for the torus heat kernel

The Gaussian series is controlled uniformly on the half-open fundamental cube.  This file contains
the summable majorant used to prove boundedness and continuity of the kernel.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
open scoped Topology
namespace RegularityStructures

def gaussianOneDimMajorant (a : ℝ) (n : ℤ) : ℝ :=
  (if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then 1 else 0) +
    exp (-(a / 4) * (n : ℝ) ^ 2)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.HolderBesov ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.KolmogorovHolderBesovHeat ====
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
# Heat-kernel input for the Kolmogorov criterion

This file records the scale-uniform Gaussian estimate used by the spatial
Kolmogorov argument.  The periodisation and normalization are those of
`RegularityStructures.Torus.HeatKernelIntegral`; the resulting estimate is the
three-dimensional heat-kernel bound behind Hairer [Hai14, (2.1)--(2.3)].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
def gaussianMajorantQuarter (n : ℤ) : ℝ :=
  gaussianOneDimMajorant (1 / 4 : ℝ) n

noncomputable def gaussianVectorMajorantConstant : ℝ :=
  ∑' k : Fin 3 → ℤ, ∏ i, gaussianMajorantQuarter (k i)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.KolmogorovHolderBesovLp ====
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
# Heat-kernel Hölder bounds on the torus

This file proves the (L^p)-to-(L^\infty) estimate used in the dyadic Kolmogorov
argument.  The pointwise heat-kernel majorant is the periodised Gaussian estimate in
`KolmogorovHolderBesovHeat`; the normalization is the one in Hairer [Hai14, (2.1)--(2.3)].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures

/-- The scale-free constant in the periodised Gaussian estimate. -/
noncomputable def heatKernelScaleConstant : ℝ :=
  (4 * Real.pi) ^ (-(3 : ℝ) / 2) * gaussianVectorMajorantConstant
axiom heatKernelScaleConstant_nonneg : 0 ≤ heatKernelScaleConstant

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.KolmogorovHolderBesovCriterion ====
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
axiom dyadicScale_pos (n : ℕ) : 0 < dyadicScale n

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.KolmogorovHolderBesovMoment ====
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
# Annealed closure of the dyadic holderBesov bound

This module turns the deterministic dyadic reduction into an explicit moment estimate.  The
endpoint moment assumptions are deliberately exposed: they are the output of the heat smoothing
estimate and Tonelli/Fubini for a random field.  This separation keeps measurability and tail
inputs visible in the theorem statement.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
def dyadicHolderBesovTerm (η : ℝ) (n : ℕ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
    ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ

axiom holderBesovENorm_natMoment_le_of_dyadic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → C(Torus3, ℝ)} {η : ℝ} {p : ℕ} (hη : η ≤ 0)
    (hp : p ≠ 0)
    (_hholder : AEMeasurable (fun ω => holderBesovENorm η (X ω)) P)
    (hterm : ∀ n : ℕ,
      AEMeasurable (fun ω => dyadicHolderBesovTerm η n (X ω)) P)
    {b : ℕ → ℝ≥0∞}
    (hbound : ∀ n : ℕ,
      ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P ≤ b n) :
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.Torus.KolmogorovHolderBesovEstimate ====
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
# Endpoint estimates for the dyadic Kolmogorov argument

The endpoint estimate makes the two analytic inputs explicit: the heat `Lᵖ` smoothing bound and
the annealed pointwise heat estimate.  The conversion between Bochner integrals and lintegrals is
kept in this module so that the final random-field theorem does not conceal an integrability
assumption.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures


axiom dyadicHeatPower_eq_geometric {p : ℕ} {α η : ℝ} (n : ℕ) :
    (dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          (dyadicScale (n + 2)) ^ (α * p / 2)) =
      heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2) *
        ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n
/- The geometric constant is written with the actual heat-kernel constant, so its dependence on
the exponent and the regularity gap is visible in the final moment theorem. -/
noncomputable def kolmogorovHolderBesovConstant (p : ℕ) (α η : ℝ) : ℝ :=
  heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2) *
    (1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2))⁻¹

axiom dyadicHolderBesovTerm_lintegral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {X : Ω → C(Torus3, ℝ)} {η α A q : ℝ} {p : ℕ}
    (hpq : (p : ℝ).HolderConjugate q)
    (hjoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      AEMeasurable
        (fun z : Ω × Torus3 =>
          ‖heatSemigroup r (X z.1) z.2‖ₑ ^ p) (P.prod volume))
    (hpoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ y : Torus3,
      ∫⁻ ω, ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2))) (n : ℕ) :
    ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P ≤
      ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))))
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_ba98e5771189710ef6ff_KolmogorovHolderBesovConclusion ====
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
# The spatial Kolmogorov moment criterion

This is the annealed-to-pathwise spatial step for the negative-order norm in
`RegularityStructures.Torus.HolderBesov`.  The decay condition is the expected
`p (α - η) > 3`; all measurability and pointwise heat-moment hypotheses are explicit.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
theorem holderBesovENorm_natMoment_le_of_pointwise {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {X : Ω → C(Torus3, ℝ)} {η α A : ℝ} {p : ℕ}
    (hη : η ≤ 0) (hp : 2 ≤ p) (hdecay : 3 < p * (α - η)) (hA : 0 ≤ A)
    (hholder : AEMeasurable (fun ω => holderBesovENorm η (X ω)) P)
    (hterm : ∀ n : ℕ,
      AEMeasurable (fun ω => dyadicHolderBesovTerm η n (X ω)) P)
    (hjoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      AEMeasurable
        (fun z : Ω × Torus3 =>
          ‖heatSemigroup r (X z.1) z.2‖ₑ ^ p) (P.prod volume))
    (hpoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ y : Torus3,
      ∫⁻ ω, ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2))) :
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤
      ENNReal.ofReal (kolmogorovHolderBesovConstant p α η * A ^ p) := by
  have hp0 : p ≠ 0 := by omega
  have hp1 : 1 < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  let q : ℝ := (p : ℝ) / ((p : ℝ) - 1)
  have hpq : (p : ℝ).HolderConjugate q := by
    dsimp [q]
    exact .conjExponent hp1
  let b : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
      (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
        (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))))
  have hdyadic :
      ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n := by
    apply holderBesovENorm_natMoment_le_of_dyadic hη hp0 hholder hterm
    intro n
    dsimp [b]
    exact dyadicHolderBesovTerm_lintegral_pow_le hpq hjoint hpoint n
  let D : ℝ := heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2)
  have hδ : 0 < (p : ℝ) * (α - η) - 3 := by linarith
  have hq_nonneg : 0 ≤ (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hq_lt : (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) < 1 := by
    apply (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
    exact Or.inr (Or.inl ⟨by norm_num, by linarith⟩)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg heatKernelScaleConstant_nonneg
      (Real.rpow_nonneg (dyadicScale_pos 2).le _)
  have hDA : 0 ≤ D * A ^ p := mul_nonneg hD (pow_nonneg hA p)
  have hgeom :
      ∀ n : ℕ, b n =
        ENNReal.ofReal (D * A ^ p) *
          (ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2))) ^ n := by
    intro n
    have hreal :
        (dyadicScale n) ^ (-η * p / 2) *
            (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
              (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))) =
          D * A ^ p * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by
      calc
        (dyadicScale n) ^ (-η * p / 2) *
              (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
                (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))) =
            ((dyadicScale n) ^ (-η * p / 2) *
              (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
                (dyadicScale (n + 2)) ^ (α * p / 2))) * A ^ p := by ring
        _ = (D * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n) * A ^ p := by
          rw [dyadicHeatPower_eq_geometric (p := p) (α := α) (η := η) n]
        _ = D * A ^ p * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by ring
    dsimp [b]
    rw [hreal, ENNReal.ofReal_mul hDA, ENNReal.ofReal_pow hq_nonneg]
  calc
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n := hdyadic
    _ = ENNReal.ofReal (D * A ^ p) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)))⁻¹ := by
      rw [show (fun n : ℕ => b n) =
          (fun n : ℕ => ENNReal.ofReal (D * A ^ p) *
            (ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2))) ^ n) by
        funext n
        exact hgeom n]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (D * A ^ p) *
        ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2))⁻¹) := by
      have hsub : (1 : ℝ≥0∞) -
          ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) =
          ENNReal.ofReal (1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hq_nonneg]
      rw [hsub, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hq_lt)]
    _ = ENNReal.ofReal (kolmogorovHolderBesovConstant p α η * A ^ p) := by
      rw [← ENNReal.ofReal_mul hDA]
      congr 1
      dsimp [kolmogorovHolderBesovConstant, D]
      ring
end RegularityStructures
end
