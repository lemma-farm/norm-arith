/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.MinMax
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Sorted
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.QuadForm
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Courant–Fischer, Weyl's inequality and continuity of eigenvalues

For a Hermitian matrix over an arbitrary finite index type we prove the min-max and max-min
characterizations of the `k`-th smallest eigenvalue, Weyl's perturbation inequality in the L²
operator norm (in counting form and for sorted eigenvalues), and continuity of each sorted
eigenvalue along a continuous family of Hermitian matrices.
-/
@[expose] public section
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace FroehlichSpencer.Infra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}
theorem eigenvalueCount_le_eigenvalueCount_add_norm (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) (E : ℝ) :
    eigenvalueCount hH' E ≤ eigenvalueCount hH (E + ‖H - H'‖) := by
  rw [← finrank_spectralSubspace_Iic hH']
  refine finrank_le_eigenvalueCount hH _ fun u hu => ?_
  have h1 := re_star_dotProduct_mulVec_le_of_mem_spectralSubspace_Iic hH' hu
  have h2 := abs_re_star_dotProduct_mulVec_le (H - H') u
  have h3 := re_star_dotProduct_sub_mulVec H H' u
  have h4 := (abs_le.mp h2).2
  linarith only [h1, h3, h4]
theorem eigenvaluesAsc_le_eigenvaluesAsc_add_norm (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    eigenvaluesAsc hH k ≤ eigenvaluesAsc hH' k + ‖H - H'‖ :=
  eigenvaluesAsc_le_add_of_eigenvalueCount_le hH hH' _
    (eigenvalueCount_le_eigenvalueCount_add_norm hH hH') k
/-- **Weyl's inequality.** -/
theorem abs_eigenvaluesAsc_sub_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    |eigenvaluesAsc hH k - eigenvaluesAsc hH' k| ≤ ‖H - H'‖ := by
  have h1 := eigenvaluesAsc_le_eigenvaluesAsc_add_norm hH hH' k
  have h2 := eigenvaluesAsc_le_eigenvaluesAsc_add_norm hH' hH k
  rw [norm_sub_rev] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩
theorem continuous_eigenvaluesAsc {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℂ}
    (hA : Continuous A) (hAH : ∀ x, (A x).IsHermitian) (k : Fin (Fintype.card ι)) :
    Continuous fun x => eigenvaluesAsc (hAH x) k := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  have hn : Filter.Tendsto (fun x => ‖A x - A x₀‖) (nhds x₀) (nhds 0) := by
    have hc : Continuous fun x => ‖A x - A x₀‖ :=
      (hA.sub (continuous_const (y := A x₀))).norm
    simpa using hc.tendsto x₀
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) hn
  rw [Real.dist_eq]
  exact abs_eigenvaluesAsc_sub_le (hAH x) (hAH x₀) k
end FroehlichSpencer.Infra
