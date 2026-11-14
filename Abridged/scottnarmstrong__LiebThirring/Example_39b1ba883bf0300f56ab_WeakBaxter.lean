module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.Inv

-- ==== Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Defs.Configuration ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Particle configurations and spin states

Spatial and spin spaces for many-particle L² states, with coordinate insertion and permutation.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
@[expose] def Position  : Type :=
  EuclideanSpace ℝ (Fin 3)
attribute [reducible] Position
@[expose] def Configuration (N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin N × Fin 3)
attribute [reducible] Configuration
@[expose] def SpinLabels (N q : ℕ) : Type :=
  Fin N → Fin q
attribute [reducible] SpinLabels
@[expose] def SpinAmplitudes (N q : ℕ) : Type :=
  EuclideanSpace ℂ (SpinLabels N q)
attribute [reducible] SpinAmplitudes
@[expose] def State (N q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))
attribute [reducible] State
@[expose] def particlePosition {N : ℕ} (x : Configuration N) (i : Fin N) : Position :=
  toLp 2 (fun a => x (i, a))

end LiebThirring
end

end

-- ==== Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Defs.Coulomb ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coulomb interactions

Electron and nuclear interactions, nearest-nucleus distances, and the electrostatic correction
in Baxter’s inequality.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
@[expose] noncomputable def coulombKernel (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹
@[expose] noncomputable def electronRepulsion {N : ℕ} (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    coulombKernel (particlePosition x i) (particlePosition x j)
@[expose] noncomputable def attraction {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k)
@[expose] noncomputable def nuclearRepulsion {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l : Fin M => k < l),
    ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l)
@[expose] noncomputable def nearestNucleusDistance {M : ℕ}
    (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ENNReal.ofReal ‖x - R k‖
@[expose] noncomputable def nearestOtherNucleusDistance {M : ℕ}
    (R : Fin M → Position) (k : Fin M) : ℝ≥0∞ :=
  ⨅ l : {l : Fin M // l ≠ k}, ENNReal.ofReal ‖R k - R l‖
@[expose] noncomputable def nearestNucleusControl {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  (2 * (Z : ℝ≥0∞) + 1) *
    ∑ i : Fin N, (nearestNucleusDistance R (particlePosition x i))⁻¹
@[expose] noncomputable def baxterCorrection {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  (Z : ℝ≥0∞) ^ 2 / 4 * ∑ k : Fin M, (nearestOtherNucleusDistance R k)⁻¹
end LiebThirring
end

end

-- ==== Examples.scottnarmstrong__LiebThirring.Examples.Example_39b1ba883bf0300f56ab_WeakBaxter ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conditional bounded-charge Baxter inequality

Weak Baxter for arbitrary bounded nonnegative charges, conditional only on the exact
equal-charge Baxter proposition.
-/
public section
open scoped ENNReal NNReal
namespace LiebThirring.Assembly


set_option linter.unusedVariables false in
/-- Weak Baxter for arbitrary bounded nonnegative charges, conditional only on
the exact equal-charge Baxter proposition. -/
theorem weakBaxter_of_baxter
    (hB : ∀ (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N),
      attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
          nearestNucleusControl Z R x)
    (N M : ℕ) (Z : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Configuration N) (hz : ∀ k, z k ≤ Z) 
    (h_LiebThirring_Assembly_attraction_zero : ∀ {N M : ℕ} (R : Fin M → LiebThirring.Position) (x : LiebThirring.Configuration N),
      LiebThirring.attraction (fun (x : Fin M) ↦ 0) R x = 0)
    (h_LiebThirring_Assembly_sum_product_weights : ∀ {ι β : Type} [inst : Fintype ι] [inst_1 : Fintype β] [inst_2 : DecidableEq ι]
      (w : ι → β → ENNReal), (∀ (i : ι), ∑ b : β, w i b = 1) → ∑ v : ι → β, ∏ i : ι, w i (v i) = 1)
    (h_LiebThirring_Assembly_averaged_attraction : ∀ {N M : ℕ} (w : Fin M → Bool → ENNReal) (c : Fin M → Bool → NNReal) (z : Fin M → NNReal)
      (R : Fin M → LiebThirring.Position) (x : LiebThirring.Configuration N),
      (∀ (k : Fin M), ∑ b : Bool, w k b = 1) →
        (∀ (k : Fin M), ∑ b : Bool, w k b * (↑(c k b) : ENNReal) = (↑(z k) : ENNReal)) →
          ∑ v : Fin M → Bool,
              (∏ k : Fin M, w k (v k)) * LiebThirring.attraction (fun (k : Fin M) ↦ c k (v k)) R x =
            LiebThirring.attraction z R x)
    (h_LiebThirring_Assembly_vertex_baxter : (∀ (N M : ℕ) (Z : NNReal) (R : Fin M → LiebThirring.Position) (x : LiebThirring.Configuration N),
        LiebThirring.attraction (fun (x : Fin M) ↦ Z) R x + LiebThirring.baxterCorrection Z R ≤
          LiebThirring.electronRepulsion x + LiebThirring.nuclearRepulsion (fun (x : Fin M) ↦ Z) R +
            LiebThirring.nearestNucleusControl Z R x) →
      ∀ (N M : ℕ) (Z : NNReal) (R : Fin M → LiebThirring.Position) (x : LiebThirring.Configuration N)
        (v : Fin M → Bool),
        LiebThirring.attraction (fun (k : Fin M) ↦ if v k = Bool.true then Z else 0) R x ≤
          LiebThirring.electronRepulsion x +
              LiebThirring.nuclearRepulsion (fun (k : Fin M) ↦ if v k = Bool.true then Z else 0) R +
            LiebThirring.nearestNucleusControl Z R x)
    (h_LiebThirring_Assembly_averaged_nuclearRepulsion : ∀ {M : ℕ} (w : Fin M → Bool → ENNReal) (c : Fin M → Bool → NNReal) (z : Fin M → NNReal)
      (R : Fin M → LiebThirring.Position),
      (∀ (k : Fin M), ∑ b : Bool, w k b = 1) →
        (∀ (k : Fin M), ∑ b : Bool, w k b * (↑(c k b) : ENNReal) = (↑(z k) : ENNReal)) →
          ∑ v : Fin M → Bool,
              (∏ k : Fin M, w k (v k)) * LiebThirring.nuclearRepulsion (fun (k : Fin M) ↦ c k (v k)) R =
            LiebThirring.nuclearRepulsion z R)
    :
    attraction z R x ≤ electronRepulsion x + nuclearRepulsion z R +
      nearestNucleusControl Z R x := by
  classical
  by_cases hZ : Z = 0
  · have hz0 : z = fun _ => 0 := funext (fun k => le_zero_iff.mp (hZ ▸ hz k))
    rw [hz0, h_LiebThirring_Assembly_attraction_zero]
    exact zero_le
  let t : Fin M → ℝ≥0 := fun k => z k / Z
  have ht (k : Fin M) : t k ≤ 1 := (div_le_one (pos_iff_ne_zero.mpr hZ)).mpr (hz k)
  let w : Fin M → Bool → ℝ≥0∞ := fun k b => if b then (t k : ℝ≥0∞) else (1 - t k : ℝ≥0)
  let c : Fin M → Bool → ℝ≥0 := fun _ b => if b then Z else 0
  have hw (k : Fin M) : ∑ b, w k b = 1 := by
    simp only [w, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le (ht k), ENNReal.coe_one]
  have hc (k : Fin M) : ∑ b, w k b * (c k b : ℝ≥0∞) = (z k : ℝ≥0∞) := by
    simp only [w, c, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
      ENNReal.coe_zero, mul_zero, add_zero, ← ENNReal.coe_mul]
    exact congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (div_mul_cancel₀ (z k) hZ)
  have hav := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    mul_le_mul_right (h_LiebThirring_Assembly_vertex_baxter hB N M Z R x v) (∏ k, w k (v k)))
  change (∑ v : Fin M → Bool, (∏ k, w k (v k)) * attraction (fun k => c k (v k)) R x) ≤
    ∑ v : Fin M → Bool, (∏ k, w k (v k)) *
      (electronRepulsion x + nuclearRepulsion (fun k => c k (v k)) R +
        nearestNucleusControl Z R x) at hav
  simp_rw [mul_add, Finset.sum_add_distrib] at hav
  rw [h_LiebThirring_Assembly_averaged_attraction w c z R x hw hc, h_LiebThirring_Assembly_averaged_nuclearRepulsion w c z R hw hc,
    ← Finset.sum_mul, ← Finset.sum_mul, h_LiebThirring_Assembly_sum_product_weights w hw, one_mul, one_mul] at hav
  exact hav
end LiebThirring.Assembly
end
