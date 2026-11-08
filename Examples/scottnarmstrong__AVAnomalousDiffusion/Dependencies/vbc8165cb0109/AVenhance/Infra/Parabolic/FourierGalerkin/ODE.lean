-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.ODE.Linear
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite real Galerkin systems for the weak form

The coordinates below are real coefficients of a finite orthonormal family of periodic modes.
The coefficient matrix records the weak form exactly: the drift entry is the integral of
`(b · D eⱼ) eᵢ`. In particular, no integration by parts is used to move the drift onto the test
mode, and no divergence-free hypothesis occurs.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
local instance galerkinMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance galerkinMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance galerkinProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Real coefficient vectors with their Euclidean inner product and norm. -/
abbrev Coefficients (n : ℕ) := PiLp 2 (fun _ : Fin n => ℝ)
variable {n : ℕ}
/-- The ordinary dot product on `Vec 2`, written without importing PDE definitions. -/
def vecDot (u v : Fin 2 → ℝ) : ℝ := ∑ k, u k * v k
/-- The weak-form matrix entry for trial mode `j` and test mode `i`.

The drift is kept in the source form `b · D eⱼ`; this definition does not rewrite it by spatial
integration by parts. -/
def weakFormMatrixEntry (b : ℝ → Torus → Fin 2 → ℝ) (κ : ℝ)
    (mode : Fin n → Torus → ℝ) (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    (t : ℝ) (i j : Fin n) : ℝ :=
  -(∫ x, vecDot (b t x) (modeGrad j x) * mode i x) -
    κ * ∫ x, vecDot (modeGrad j x) (modeGrad i x)
/-- The coefficients of an L² projection onto a finite real orthonormal mode family. -/
def modeProjectionCoefficients (n : ℕ) (mode : Fin n → Torus → ℝ)
    (f : Torus → ℝ) : Coefficients n :=
  WithLp.toLp 2 (fun i => ∫ x, f x * mode i x)
/-- The function represented by a finite real coefficient vector. -/
def modeExpansion (n : ℕ) (mode : Fin n → Torus → ℝ)
    (c : Coefficients n) (x : Torus) : ℝ :=
  ∑ i, c i * mode i x
/-- Finite-dimensional weak-form ODE data on a finite real mode family.

`coefficient` is understood as the bounded measurable extension of the Galerkin matrix from the
closed time interval to the line, as required by `LinearODEData`. `matrix_spec` fixes its values on
the physical time interval to the weak-form entries. `mode_orthonormal` makes the coefficient
derivative equal to the tested weak equation without a mass matrix. -/
structure WeakFormGalerkinData (n : ℕ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  mode : Fin n → Torus → ℝ
  modeGrad : Fin n → Torus → Fin 2 → ℝ
  mode_orthonormal : ∀ i j,
    ∫ x, mode i x * mode j x = if i = j then 1 else 0
  frequencyCutoff : ℕ
  modeExpansion_fixed_by_projection : ∀ c x,
    realFourierProjection frequencyCutoff (modeExpansion n mode c) x =
      modeExpansion n mode c x
  initialData : Torus → ℝ
  drift : ℝ → Torus → Fin 2 → ℝ
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  initial : Coefficients n
  coefficient : ℝ → Coefficients n →L[ℝ] Coefficients n
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficient_aestronglyMeasurable : AEStronglyMeasurable coefficient volume
  coefficient_norm_le : ∀ t, ‖coefficient t‖ ≤ coefficientBound
  matrix_spec : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c i,
    coefficient t c i =
      ∑ j, weakFormMatrixEntry drift diffusivity mode modeGrad t i j * c j
  initial_is_projection : initial = modeProjectionCoefficients n mode initialData
  projection_eq_modeExpansion : ∀ x,
    modeExpansion n mode initial x =
      realFourierProjection frequencyCutoff initialData x
  gradient : Coefficients n →L[ℝ] F
  driftBound : ℝ
  driftForm : ℝ → Coefficients n → ℝ
  weakForm_energy : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c,
    2 * inner ℝ c (coefficient t c) =
      -2 * driftForm t c - 2 * diffusivity * ‖gradient c‖ ^ 2
  drift_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c,
    |driftForm t c| ≤ driftBound * ‖gradient c‖ * ‖c‖
namespace WeakFormGalerkinData
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end WeakFormGalerkinData
end AVenhance.Infra.Parabolic.FourierGalerkin
end
