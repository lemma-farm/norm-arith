/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Defs.Coulomb
import Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Kinetic.DensityBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Extended Coulomb measurability and endpoints

Measurability and endpoint identities for extended Coulomb interactions, including singular
values and zero charges.
-/
public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Assembly
theorem attraction_zero {N M : ℕ} (R : Fin M → Position) (x : Configuration N) :
    attraction (fun _ => 0) R x = 0 := by
  simp only [attraction, ENNReal.coe_zero, zero_mul, Finset.sum_const_zero]
theorem nearestNucleusDistance_restrict_le {M m : ℕ} (R : Fin M → Position)
    (e : Fin m → Fin M) (x : Position) :
    nearestNucleusDistance R x ≤ nearestNucleusDistance (R ∘ e) x := by
  exact le_iInf (fun j => iInf_le _ (e j))
theorem nearestNucleusControl_restrict_le {N M m : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (e : Fin m → Fin M) (x : Configuration N) :
    nearestNucleusControl Z (R ∘ e) x ≤ nearestNucleusControl Z R x := by
  apply mul_le_mul_right
  exact Finset.sum_le_sum (fun i _ =>
    ENNReal.inv_le_inv.mpr (nearestNucleusDistance_restrict_le R e _))
theorem attraction_restrict {N M m : ℕ} (I : Set (Fin M)) (e : Fin m ≃ I)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Configuration N)
    (hz : ∀ k, k ∉ I → z k = 0) :
    attraction z R x =
      attraction (fun j => z (e j).val) (fun j => R (e j).val) x := by
  classical
  unfold attraction
  apply Finset.sum_congr rfl
  intro i _
  have hf : ∀ k, k ∉ I →
      (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k) = 0 := by
    intro k hk
    rw [hz k hk, ENNReal.coe_zero, zero_mul]
  calc
    _ = ∑ k : I, (z k.val : ℝ≥0∞) *
        coulombKernel (particlePosition x i) (R k.val) :=
      Finset.sum_congr_set I _ _ (fun _ _ => rfl) hf
    _ = _ := (e.sum_comp _).symm
end LiebThirring.Assembly
end
