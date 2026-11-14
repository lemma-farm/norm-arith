module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.BigOperators.Ring.Finset

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v4c18d13601f3.RegularityStructures.Torus.Basic ====
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v4c18d13601f3.RegularityStructures.Torus.HolderBesovLittlewoodPaley ====
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
# Explicit periodic Littlewood--Paley blocks

For the comparison with the heat norm (2.3) of the statement, choose a smooth one-dimensional cutoff
equal to one on `[-1,1]` and zero outside `(-2,2)`, and take its tensor product in Fourier space.
The low-frequency symbol at level `n` is the cutoff at frequency scale `2^n`; consecutive
differences give the dyadic blocks. The finite frequency box contains the whole support of each
symbol.

These are literal Fourier multiplier formulas, using Mathlib's normalized torus Fourier
coefficients. The extended norm is the standard inhomogeneous `B^η_{∞,∞}` dyadic expression
for this fixed cutoff; this module does not yet prove equivalence with the heat norm.
-/
@[expose] public noncomputable section
open scoped ENNReal
open UnitAddTorus
namespace RegularityStructures
/-- A fixed smooth cutoff with inner radius one and outer radius two. -/
def torusLPBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩
/-- The tensor-product low-frequency symbol at frequency scale `2^n`. -/
def torusLowFrequencySymbol (n : ℕ) (k : Fin 3 → ℤ) : ℝ :=
  ∏ i : Fin 3, torusLPBump (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ))
/-- Low frequencies at level zero, then consecutive low-frequency differences. -/
def torusDyadicFrequencySymbol : ℕ → (Fin 3 → ℤ) → ℝ
  | 0, k => torusLowFrequencySymbol 0 k
  | n + 1, k => torusLowFrequencySymbol (n + 1) k - torusLowFrequencySymbol n k
/-- A finite integer-frequency cube containing the level-`n` symbol support. -/
def torusLPFrequencyBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 =>
    Finset.Icc (-((2 ^ (n + 1) : ℕ) : ℤ)) ((2 ^ (n + 1) : ℕ) : ℤ)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v4c18d13601f3.RegularityStructures.Torus.HolderBesovMultiplierProfiles ====
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
# Fixed Schwartz profiles for the heat/Besov comparison

The tensor cutoff and the localized inverse heat multiplier are smooth compactly supported
profiles. In scaled frequency coordinates the latter is `cutoff(u) exp(4 π² τ u²)`;
the parameters needed for consecutive dyadic levels are fixed (`τ = 1` and `τ = 1/4`).
Consequently the preceding Poisson multiplier bound is uniform in the dyadic level.

These are the actual cutoff profiles, not multiplier hypotheses.
-/
@[expose] public noncomputable section
open scoped ENNReal SchwartzMap
namespace RegularityStructures
open scoped ContDiff in
/-- The fixed one-dimensional complexified frequency cutoff, as a Schwartz function. -/
def torusLPCutoffProfile : 𝓢(ℝ, ℂ) :=
  (torusLPBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp torusLPBump.contDiff)

open scoped ContDiff in
/-- The fixed compactly supported inverse-heat frequency multiplier profile. -/
def torusLPInverseHeatProfile (τ : ℝ) : 𝓢(ℝ, ℂ) :=
  (show HasCompactSupport (fun u : ℝ => (torusLPBump u : ℂ) *
      Complex.exp ((4 * Real.pi ^ 2 * τ * u ^ 2 : ℝ) : ℂ)) from
    (torusLPBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).mul_right).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp torusLPBump.contDiff).mul
        (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp
          (contDiff_const.mul (contDiff_id.pow 2)))))

axiom torusLPInverseHeatProfile_eq_zero (τ : ℝ) {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPInverseHeatProfile τ u = 0
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v4c18d13601f3.RegularityStructures.Torus.HolderBesovCutoffKernel ====
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
# Uniform bounds for the actual finite dyadic multiplier kernels

For profiles supported in `[-2,2]`, the dyadic frequency cube contains every nonzero
sample. Finite-product expansion identifies the finite three-dimensional Fourier sum
with the product of the one-dimensional Schwartz multiplier series. Poisson summation
then gives the scale-independent L1 bound for the literal LP cutoffs.

This is the Fourier multiplier estimate used in the equivalence of the heat norm (2.3) of the
statement with the Littlewood--Paley norm.
-/
@[expose] public noncomputable section
open MeasureTheory Set UnitAddTorus
open scoped ENNReal SchwartzMap
namespace RegularityStructures
/-- A finite tensor-profile Fourier kernel at frequency scale `2^n`. -/
def torusTensorFiniteKernel (m : Fin 3 → 𝓢(ℝ, ℂ)) (n : ℕ) : C(Torus3, ℂ) :=
  ∑ k ∈ torusLPFrequencyBox n,
    (∏ i : Fin 3, m i ((k i : ℝ) / (2 : ℝ) ^ n)) • mFourier k

axiom torusTensorFiniteKernel_bound_uniform (m : Fin 3 → 𝓢(ℝ, ℂ))
    (hm : ∀ i u, 2 ≤ |u| → m i u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x : Torus3, ‖torusTensorFiniteKernel m n x‖ₑ) ≤ ENNReal.ofReal C
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_58dceaff9bc851d32563_HolderBesovInverseHeatKernel ====
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
# Uniform kernels for the dyadic inverse-heat multiplier

At time `s = 2^(-2n)`, the inverse heat multiplier is a fixed smooth profile in frequency
coordinates `k/2^n`. Localising to the actual LP block gives a uniform L1 bound. The two consecutive
cutoffs use the fixed profiles with parameters `1` and `1/4`. This is the inverse-multiplier step in
the comparison of the LP norm with the heat norm (2.3) of the statement.
-/
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus
open scoped ENNReal SchwartzMap
namespace RegularityStructures
/-- The inverse heat character at time `2^(-2n)`, factored by coordinate. -/
def torusInverseHeatWeight (n : ℕ) (k : Fin 3 → ℤ) : ℂ :=
  ∏ i : Fin 3, Complex.exp ((4 * Real.pi ^ 2 *
    (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ)) ^ 2 : ℝ) : ℂ)
/-- The literal dyadic symbol multiplied by the inverse heat character. -/
def torusDyadicInverseHeatKernel (n : ℕ) : C(Torus3, ℂ) :=
  ∑ k ∈ torusLPFrequencyBox n,
    ((torusDyadicFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k) • mFourier k
private def innerInverseHeatProfile : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ 2 (by norm_num)).toContinuousLinearEquiv
      (torusLPInverseHeatProfile (1 / 4))

private axiom innerInverseHeatProfile_eq_zero {u : ℝ} (hu : 2 ≤ |u|) :
    innerInverseHeatProfile u = 0

private axiom inverseKernel_zero :
    torusDyadicInverseHeatKernel 0 =
      torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) 0
private axiom inverseKernel_succ (n : ℕ) :
    torusDyadicInverseHeatKernel (n + 1) =
      torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) (n + 1) -
        torusTensorFiniteKernel (fun _ : Fin 3 => innerInverseHeatProfile) (n + 1)
theorem lintegral_torusDyadicInverseHeatKernel_bound_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x : Torus3, ‖torusDyadicInverseHeatKernel n x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := torusTensorFiniteKernel_bound_uniform
    (fun _ : Fin 3 => torusLPInverseHeatProfile 1)
    (fun _ _ hu => torusLPInverseHeatProfile_eq_zero 1 hu)
  obtain ⟨C₁, hC₁, hb₁⟩ := torusTensorFiniteKernel_bound_uniform
    (fun _ : Fin 3 => innerInverseHeatProfile)
    (fun _ _ hu => innerInverseHeatProfile_eq_zero hu)
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, fun n => ?_⟩
  rw [ENNReal.ofReal_add hC₀ hC₁]
  cases n with
  | zero =>
    rw [inverseKernel_zero]
    exact (hb₀ 0).trans (le_add_of_nonneg_right zero_le)
  | succ n =>
    rw [inverseKernel_succ]
    calc
      _ ≤ ∫⁻ x : Torus3,
          ‖torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) (n + 1) x‖ₑ +
          ‖torusTensorFiniteKernel (fun _ : Fin 3 => innerInverseHeatProfile) (n + 1) x‖ₑ := by
        apply lintegral_mono
        intro x
        exact enorm_sub_le
      _ = _ := lintegral_add_left
        (torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1)
          (n + 1)).continuous.enorm.measurable _
      _ ≤ _ := add_le_add (hb₀ (n + 1)) (hb₁ (n + 1))
end RegularityStructures
end
