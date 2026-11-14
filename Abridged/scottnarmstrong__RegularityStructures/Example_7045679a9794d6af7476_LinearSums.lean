module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vf7e0101b654b.RegularityStructures.Torus.Basic ====
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
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vf7e0101b654b.RegularityStructures.Probability.WhiteNoise ====
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
# Space-time white noise

A space-time white noise on `ℝ × T³` is a family `(W(h))` of real random variables, indexed by
square-integrable functions `h`, such that every finite subfamily is a centred Gaussian vector with
covariance `E[W(hᵢ) W(hⱼ)] = ∫ hᵢ hⱼ` (the statement, Definition 2.2).

Measurability is stated explicitly. In Mathlib, `Measure.map` of a non-measurable map is a point
mass, which counts as Gaussian, and the Bochner integral of a non-measurable function is zero.
Without the measurability clauses, a non-measurable family could satisfy the remaining conditions.

Source: the statement, Definition 2.2.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures
variable {Ω : Type*} [MeasurableSpace Ω]
/-- `X` is a centred Gaussian vector in `ℝⁿ` with covariance matrix `C` under `P`: it is
a.e.-measurable, its law is Gaussian, and it has mean zero and covariance `C`. -/
def IsCentredGaussianVector (P : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ)
    (C : Fin n → Fin n → ℝ) : Prop :=
  AEMeasurable X P ∧ ProbabilityTheory.IsGaussian (P.map X) ∧ (∀ i, ∫ ω, X ω i ∂P = 0) ∧
    ∀ i j, ∫ ω, X ω i * X ω j ∂P = C i j
/-- `W` is a space-time white noise on `ℝ × T³` under `P`: each `W h` with `h` square-integrable
is a random variable, and every finite family is a centred Gaussian vector with covariance
`∫ hᵢ hⱼ`. -/
def IsWhiteNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) : Prop :=
  (∀ h : SpaceTime → ℝ, MemLp h 2 → Measurable (W h)) ∧
    ∀ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) →
      IsCentredGaussianVector P (fun ω i => W (h i) ω) fun i j => ∫ z, h i z * h j z
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vf7e0101b654b.RegularityStructures.Probability.GaussianVector ====
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
# Centred Gaussian vectors

Basic facts about `IsCentredGaussianVector P X C` (`RegularityStructures.Probability.WhiteNoise`):

* `X` has a Gaussian law, so `P` is a probability measure and every coordinate has moments of
  all orders;
* the covariance matrix `C` is symmetric;
* every linear form `∑ₘ aₘ X_{σ m}` is a centred real Gaussian with variance
  `∑ₘ ∑ₘ' aₘ aₘ' C_{σ m, σ m'}`, so its fourth and sixth moments are `3 v²` and `15 v³`;
* the law of `-X` is the law of `X`, so `E[g(X)] = 0` for every measurable odd `g`; in particular
  `E[Xᵢ Xⱼ Xₖ] = 0`.

It also records that a white noise lives on a probability space
(`IsWhiteNoise.isProbabilityMeasure`).
-/
public section
open MeasureTheory ProbabilityTheory
namespace RegularityStructures.IsCentredGaussianVector
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-! ### Linear forms -/
section Linear
variable {ι : Type*} [Fintype ι]

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.IsCentredGaussianVector.integral_linear_sq.{w_u_1,w_u_2} : ∀ {Ω : Type w_u_1} [inst : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {n : ℕ}
  {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ} {ι : Type w_u_2} [inst_1 : Fintype ι],
  RegularityStructures.IsCentredGaussianVector P X C →
    ∀ (σ : ι → Fin n) (a : ι → ℝ),
      ∫ (ω : Ω), (∑ m : ι, a m * X ω (σ m)) ^ 2 ∂P = ∑ m : ι, ∑ m' : ι, a m * a m' * C (σ m) (σ m')
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.IsCentredGaussianVector.integrable_linear_pow.{w_u_1,w_u_2} : ∀ {Ω : Type w_u_1} [inst : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {n : ℕ}
  {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ} {ι : Type w_u_2} [inst_1 : Fintype ι],
  RegularityStructures.IsCentredGaussianVector P X C →
    ∀ (σ : ι → Fin n) (a : ι → ℝ) (k : ℕ),
      MeasureTheory.Integrable (fun (ω : Ω) ↦ (∑ m : ι, a m * X ω (σ m)) ^ k) P

end Linear
/-! ### Symmetry of the law and odd moments -/
end RegularityStructures.IsCentredGaussianVector
namespace RegularityStructures.IsWhiteNoise
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

end RegularityStructures.IsWhiteNoise
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_7045679a9794d6af7476_LinearSums ====
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
# Finite linear combinations of white-noise evaluations

The finite-dimensional covariance clause forces a white-noise family to respect scalar
multiplication almost surely.  Together with `whiteNoise_add_ae`, this gives the finite-sum
identity used by Fourier partial sums.
-/
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace RegularityStructures.Phi43
theorem whiteNoise_smul_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime)) (a : ℝ) :
    (fun w => W (a • h) w) =ᵐ[P] fun w => a * W h w := by
  let f : Fin 2 → SpaceTime → ℝ := fun i => if i = 0 then a • h else h
  let b : Fin 2 → ℝ := fun i => if i = 0 then 1 else -a
  have hf : ∀ i, MemLp (f i) 2 (volume : Measure SpaceTime) := by
    intro i
    fin_cases i <;> simp [f, hh, hh.const_smul]
  have hcent := hW.2 2 f hf
  have hzero : ∫ w, (∑ i, b i * W (f i) w) ^ (2 : ℕ) ∂P = 0 := by
    calc
      ∫ w, (∑ i, b i * W (f i) w) ^ (2 : ℕ) ∂P =
          ∑ i, ∑ j, b i * b j * ∫ z, f i z * f j z :=
        hcent.integral_linear_sq (σ := id) b
      _ = 0 := by
        have hsq : Integrable (fun z : SpaceTime => h z * h z) :=
          hh.integrable_mul hh
        have h00 : (∫ z, (a • h) z * (a • h) z) =
            a ^ 2 * ∫ z, h z * h z := by
          calc
            (∫ z, (a • h) z * (a • h) z) =
                ∫ z, a ^ 2 * (h z * h z) := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  simp only [Pi.smul_apply]
                  ring
            _ = a ^ 2 * ∫ z, h z * h z := integral_const_mul _ _
        have h01 : (∫ z, (a • h) z * h z) = a * ∫ z, h z * h z := by
          calc
            (∫ z, (a • h) z * h z) = ∫ z, a * (h z * h z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [Pi.smul_apply]
              ring
            _ = a * ∫ z, h z * h z := integral_const_mul _ _
        have h10 : (∫ z, h z * (a • h) z) = a * ∫ z, h z * h z := by
          calc
            (∫ z, h z * (a • h) z) = ∫ z, a * (h z * h z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [Pi.smul_apply]
              ring
            _ = a * ∫ z, h z * h z := integral_const_mul _ _
        have h00' : (∫ z, a * h z * (a * h z)) =
            a ^ 2 * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h00
        have h01' : (∫ z, a * h z * h z) =
            a * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h01
        have h10' : (∫ z, h z * (a * h z)) =
            a * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h10
        simp [f, b, Fin.sum_univ_two]
        rw [h00', h01', h10']
        ring
  have hint : Integrable (fun w => (∑ i, b i * W (f i) w) ^ (2 : ℕ)) P :=
    hcent.integrable_linear_pow (σ := id) b 2
  have hnonneg : 0 ≤ᵐ[P] (fun w => (∑ i, b i * W (f i) w) ^ (2 : ℕ)) :=
    ae_of_all _ fun w => sq_nonneg _
  have hsumzero : (fun w => ∑ i, b i * W (f i) w) =ᵐ[P] 0 := by
    have hpow := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    filter_upwards [hpow] with w hw
    exact sq_eq_zero_iff.mp hw
  filter_upwards [hsumzero] with w hw
  have hw' : W (a • h) w - a * W h w = 0 := by
    simpa [f, b, Fin.sum_univ_two, sub_eq_add_neg] using hw
  exact sub_eq_zero.mp hw'
end RegularityStructures.Phi43
end
