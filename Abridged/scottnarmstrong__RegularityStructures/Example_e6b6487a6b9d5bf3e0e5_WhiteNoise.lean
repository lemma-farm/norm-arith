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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v249a415973ab.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v249a415973ab.RegularityStructures.Probability.WhiteNoise ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v249a415973ab.RegularityStructures.Probability.GaussianVector ====
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

end Linear
/-! ### Symmetry of the law and odd moments -/
end RegularityStructures.IsCentredGaussianVector
namespace RegularityStructures.IsWhiteNoise
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

end RegularityStructures.IsWhiteNoise
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_e6b6487a6b9d5bf3e0e5_WhiteNoise ====
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
# The L² isometry of an arbitrary white noise

The strengthened white-noise predicate supplies measurable Gaussian coordinates for every
square-integrable kernel.  The finite-dimensional covariance clause then gives the exact L²
isometry and the almost-sure identification of evaluations of equal kernels.  These are the
probabilistic identities used when a smooth Fourier series is compared with the original field.
-/
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace RegularityStructures.Phi43
theorem whiteNoise_integral_sub_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    ∫ ω, (W h ω - W g ω) ^ (2 : ℕ) ∂P = ∫ z, (h z - g z) ^ (2 : ℕ) := by
  let f : Fin 2 → SpaceTime → ℝ := fun i => if i = 0 then h else g
  let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  have hf : ∀ i, MemLp (f i) 2 (volume : Measure SpaceTime) := by
    intro i
    fin_cases i <;> simp [f, hh, hg]
  have hcent := hW.2 2 f hf
  have hlin := hcent.integral_linear_sq (σ := id) a
  have hright :
      (∑ m, ∑ m', a m * a m' * ∫ z, f m z * f m' z) =
        ∫ z, (h z - g z) ^ (2 : ℕ) := by
    have hrhs :
        (∫ z, (h z - g z) ^ (2 : ℕ)) =
          ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
      calc
        (∫ z, (h z - g z) ^ (2 : ℕ)) =
            ∫ z, h z * h z - h z * g z - g z * h z + g z * g z := by
              congr 1
              funext z
              ring
        _ = ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
              have hhh := hh.integrable_mul hh
              have hhg := hh.integrable_mul hg
              have hgh := hg.integrable_mul hh
              have hgg := hg.integrable_mul hg
              change (∫ z, ((h * h - h * g - g * h) z + (g * g) z)) = _
              rw [integral_add ((hhh.sub hhg).sub hgh) hgg]
              change (∫ z, ((h * h - h * g) z - (g * h) z)) + _ = _
              rw [integral_sub (hhh.sub hhg) hgh]
              change ((∫ z, ((h * h) z - (h * g) z)) - _) + _ = _
              rw [integral_sub hhh hhg]
              simp only [Pi.mul_apply]
    calc
      (∑ m, ∑ m', a m * a m' * ∫ z, f m z * f m' z) =
          ((∫ z, h z * h z) - (∫ z, h z * g z)) -
            (∫ z, g z * h z) + (∫ z, g z * g z) := by
              simp [f, a, Fin.sum_univ_two]
              ring
      _ = ∫ z, (h z - g z) ^ (2 : ℕ) := hrhs.symm
  rw [← hright]
  convert hlin using 1
  · simp [f, a, Fin.sum_univ_two, sub_eq_add_neg]
  · exact rfl
end RegularityStructures.Phi43
end
