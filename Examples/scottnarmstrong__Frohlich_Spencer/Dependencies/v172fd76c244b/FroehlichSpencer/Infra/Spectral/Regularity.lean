/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Weyl
public import Mathlib
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Regularity of spectral conditions

For a continuous (resp. measurable) family of Hermitian matrices, the eigenvalues are continuous
(resp. measurable), the spectral distance `min_i |λ_i - E|` is continuous, the spectral-gap events
are closed (resp. measurable), and the eigenvalue counting functions are measurable, also jointly
in the parameter and the energy. We also treat the family `v ↦ A + diagonal (v ∘ f)`.

This gives measurability of the events in Fröhlich–Spencer (1983) defined by
`dist(spec H, E) ≥ …` and of the counting function `N_Λ(E, v)`.
-/
@[expose] public section
open Matrix Finset
namespace FroehlichSpencer.Infra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*}
section Topological
variable [TopologicalSpace X] {A : X → Matrix ι ι ℂ}
end Topological
section Measurable
variable [MeasurableSpace X] {A : X → Matrix ι ι ℂ}
/-- The Hermitian part of a matrix. -/
private noncomputable def hermPart (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (2⁻¹ : ℝ) • (M + Mᴴ)
omit [Fintype ι] [DecidableEq ι] in
private theorem isHermitian_hermPart (M : Matrix ι ι ℂ) : (hermPart M).IsHermitian := by
  unfold hermPart
  rw [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  simp
omit [Fintype ι] [DecidableEq ι] in
private theorem hermPart_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  unfold hermPart
  rw [hM.eq, ← two_smul ℝ M, smul_smul]
  norm_num
omit [Fintype ι] [DecidableEq ι] in
private theorem continuous_hermPart : Continuous (hermPart (ι := ι)) := by
  unfold hermPart
  exact ((continuous_id (X := Matrix ι ι ℂ)).add continuous_id.matrix_conjTranspose).const_smul
    ((2⁻¹ : ℝ))
theorem measurable_eigenvaluesAsc (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian)
    (k : Fin (Fintype.card ι)) : Measurable fun x => eigenvaluesAsc (hAH x) k := by
  have hc : Continuous fun M : Matrix ι ι ℂ => eigenvaluesAsc (isHermitian_hermPart M) k :=
    continuous_eigenvaluesAsc continuous_hermPart isHermitian_hermPart k
  have : (fun x => eigenvaluesAsc (hAH x) k) =
      fun x => eigenvaluesAsc (isHermitian_hermPart (A x)) k := by
    funext x
    rw [eigenvaluesAsc_congr (hAH x) (isHermitian_hermPart (A x))
      (hermPart_of_isHermitian (hAH x)).symm]
  rw [this]
  exact hc.measurable.comp hA
theorem measurable_eigenvalues (hA : Measurable A) (hAH : ∀ x, (A x).IsHermitian) (i : ι) :
    Measurable fun x => (hAH x).eigenvalues i := by
  have : (fun x => (hAH x).eigenvalues i) =
      fun x => eigenvaluesAsc (hAH x) (ascIndex ι i) :=
    funext fun x => eigenvalues_eq_eigenvaluesAsc_ascIndex (hAH x) i
  rw [this]
  exact measurable_eigenvaluesAsc hA hAH _
end Measurable
section DiagonalFamily
variable {J : Type*}
omit [Fintype ι] in
theorem isHermitian_add_diagonal {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℝ) :
    (A + diagonal (fun i => (v i : ℂ))).IsHermitian := by
  refine hA.add ?_
  rw [IsHermitian, diagonal_conjTranspose]
  simp
omit [Fintype ι] in
theorem measurable_add_diagonal_comp (A : Matrix ι ι ℂ) (f : ι → J) :
    Measurable fun v : J → ℝ => A + diagonal (fun i => (v (f i) : ℂ)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, diagonal_apply_eq]
    exact measurable_const.add
      (Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (f i)))
  · simp [diagonal_apply_ne _ h]
end DiagonalFamily
end FroehlichSpencer.Infra
