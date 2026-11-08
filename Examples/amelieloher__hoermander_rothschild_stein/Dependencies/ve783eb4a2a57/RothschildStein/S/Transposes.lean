-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.fieldDerivative
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.fieldTranspose
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.wordTransposeTest
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.wordTranspose
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
/-- Coordinate expansion of a linear differential (BB (2.2), p. 68). -/
theorem differential_coordinates (A : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    A v = ∑ j : Fin n, v j * A (Hormander.Interface.basisVec j) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : Pi.single j (v j) = v j • Hormander.Interface.basisVec j := by
    ext k
    by_cases hk : k = j <;> simp [Hormander.Interface.basisVec, hk]
  rw [h, map_smul]
  rfl
/-- The scalar transpose is minus the field derivative minus divergence
(BB (2.3), p. 68). -/
theorem fieldTranspose_formula (V : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hV : DifferentiableAt ℝ V x) (hφ : DifferentiableAt ℝ φ x) :
    fieldTranspose V φ x = -fieldDerivative V φ x -
      φ x * Hormander.Interface.euclideanDivergence V x := by
  unfold fieldTranspose Hormander.Interface.euclideanDivergence fieldDerivative
  rw [fderiv_fun_smul hφ hV]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [differential_coordinates (fderiv ℝ φ x) (V x)]
  simp_rw [mul_comm (V x _) (fderiv ℝ φ x _)]
  ring
theorem fieldTransposeTest_apply (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ) :
    fieldTransposeTest Ω V hV φ x = fieldTranspose V φ x := by
  have hd : ∀ j : Fin n, DifferentiableAt ℝ (fun y => φ y * V y j) x := by
    intro j
    exact (testMultiplierOn Ω (fun y => V y j)
      ((contDiff_apply ℝ (fun _ => ℝ) j).comp_contDiffOn hV) φ).contDiff.differentiable
        (by simp) |>.differentiableAt
  unfold fieldTransposeTest fieldTranspose Hormander.Interface.euclideanDivergence
  simp only [neg_apply]
  congr 1
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ j : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j)
    (testMultiplierOn Ω (fun y => V y j)
      ((contDiff_apply ℝ (fun _ => ℝ) j).comp_contDiffOn hV) φ) :
        TestFunction Ω ℝ (⊤ : ℕ∞)) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun y => φ y * V y j) x _ = _
  rw [(hd j).lineDeriv_eq_fderiv]
  change fderiv ℝ (fun y => φ y * V y j) x _ = _
  change _ = fderiv ℝ (fun y j => φ y * V y j) x (Hormander.Interface.basisVec j) j
  rw [fderiv_pi hd]
  rfl
/-- Function coercion of the bundled transpose (BB (2.2), p. 68). -/
theorem fieldTransposeTest_coe (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (fieldTransposeTest Ω V hV φ : (Fin n → ℝ) → ℝ) = fieldTranspose V φ :=
  funext (fieldTransposeTest_apply Ω V hV φ)
/-- Scalar transpose never enlarges test support (BB (2.2), p. 68). -/
theorem tsupport_fieldTranspose_subset
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) :
    tsupport (fieldTranspose V φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hz : fderiv ℝ (fun y => φ y • V y) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => h
      ((tsupport_fderiv_subset ℝ).trans (tsupport_smul_subset_left φ V) ht))
  exact hx (by simp [fieldTranspose, Hormander.Interface.euclideanDivergence, hz])
end RothschildStein.S
