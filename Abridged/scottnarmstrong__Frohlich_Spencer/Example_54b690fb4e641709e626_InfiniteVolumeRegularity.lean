module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_54b690fb4e641709e626_InfiniteVolumeRegularity ====
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
# Infinite-volume solution: continuity in `z`, measurability in the potential

For families of square-summable solutions of `∑' w, a x w * ψ w + (v x - z) * ψ x = δ_y x`
(generic Hermitian kernel of finite row support and bounded row sums) we prove Lipschitz dependence
on `z` in `ℓ²`, continuity of `z ↦ ψ_z(x)` on `{Im z ≠ 0}`, and measurability of `v ↦ ψ_v(x)` for
the product σ-algebra on `X → ℝ` (countable `X`).

No Green function is defined here.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/
@[expose] public section
open Filter Topology
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

omit [DecidableEq X] in
private axiom summable_norm_sq' {ψ : X → ℂ} (hψ : Memℓp ψ 2) :
    Summable fun x => ‖ψ x‖ ^ 2
/-- Lipschitz dependence on `z` in `ℓ²`. -/
axiom tsum_norm_sq_sub_le_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {y : X} {ψ ψ' : X → ℂ}
    (hψ : Memℓp ψ 2)
    (hψeq : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x)
    (hψ' : Memℓp ψ' 2)
    (hψ'eq : ∀ x, ∑' w, a x w * ψ' w + ((v x : ℂ) - z') * ψ' x = (Pi.single y 1 : X → ℂ) x) :
    ∑' x, ‖ψ x - ψ' x‖ ^ 2 ≤ ‖z - z'‖ ^ 2 / (z.im ^ 2 * z'.im ^ 2)
/-- Continuity in `z` of any family of `ℓ²` solutions. -/
theorem continuousOn_of_forall_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) (y x : X) {Ψ : ℂ → X → ℂ}
    (hΨ : ∀ z, z.im ≠ 0 → Memℓp (Ψ z) 2 ∧
      ∀ x', ∑' w, a x' w * Ψ z w + ((v x' : ℂ) - z) * Ψ z x' = (Pi.single y 1 : X → ℂ) x') :
    ContinuousOn (fun z => Ψ z x) {z | z.im ≠ 0} := by
  intro z0 hz0
  have hz0' : z0.im ≠ 0 := hz0
  have hp : 0 < |z0.im| := abs_pos.2 hz0'
  set C : ℝ := 2 / z0.im ^ 2 with hC
  have hev : ∀ᶠ z in 𝓝[{z | z.im ≠ 0}] z0, ‖Ψ z x - Ψ z0 x‖ ≤ C * ‖z - z0‖ := by
    have hball : ∀ᶠ z in 𝓝 z0, ‖z - z0‖ < |z0.im| / 2 := by
      have : Tendsto (fun z : ℂ => ‖z - z0‖) (𝓝 z0) (𝓝 ‖z0 - z0‖) :=
        ((continuous_id.sub continuous_const).norm).tendsto z0
      simp only [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hzb hzs
    have hzs' : z.im ≠ 0 := hzs
    have himz : |z0.im| / 2 ≤ |z.im| := by
      have : |z0.im - z.im| ≤ ‖z - z0‖ := by
        rw [abs_sub_comm]
        simpa using Complex.abs_im_le_norm (z - z0)
      have h2 := abs_sub_abs_le_abs_sub z0.im z.im
      linarith only [this, h2, hzb]
    have hsq := tsum_norm_sq_sub_le_of_eq_single ha hfin hK v hzs' hz0' (ψ := Ψ z) (ψ' := Ψ z0)
      (hΨ z hzs').1 (hΨ z hzs').2 (hΨ z0 hz0').1 (hΨ z0 hz0').2
    have hxle : ‖Ψ z x - Ψ z0 x‖ ^ 2 ≤ ∑' x, ‖Ψ z x - Ψ z0 x‖ ^ 2 :=
      (summable_norm_sq' ((hΨ z hzs').1.sub (hΨ z0 hz0').1)).le_tsum x fun j _ => by positivity
    have hzz : 0 < z.im ^ 2 := by positivity
    have hzz0 : 0 < z0.im ^ 2 := by positivity
    have hlow : z0.im ^ 2 ≤ 4 * z.im ^ 2 := by
      have := mul_self_le_mul_self (by positivity) himz
      rw [← sq_abs z.im, ← sq_abs z0.im]
      nlinarith only [this]
    have hfin2 : ‖z - z0‖ ^ 2 / (z.im ^ 2 * z0.im ^ 2) ≤ (C * ‖z - z0‖) ^ 2 := by
      rw [div_le_iff₀ (by positivity), hC, mul_pow, div_pow, ← pow_mul]
      have h4 : 0 ≤ ‖z - z0‖ ^ 2 := sq_nonneg _
      have : (2 : ℝ) ^ 2 / z0.im ^ (2 * 2) * ‖z - z0‖ ^ 2 * (z.im ^ 2 * z0.im ^ 2) =
          4 * z.im ^ 2 / z0.im ^ 2 * ‖z - z0‖ ^ 2 := by
        field_simp
        ring
      rw [this]
      have h5 : 1 ≤ 4 * z.im ^ 2 / z0.im ^ 2 := by
        rw [le_div_iff₀ hzz0]; linarith only [hlow]
      nlinarith only [h5, h4]
    exact le_of_sq_le_sq (hxle.trans (hsq.trans hfin2)) (by positivity)
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero_norm' (a := fun z => C * ‖z - z0‖) ?_ ?_)
  · filter_upwards [hev] with z hz
    simpa [norm_norm] using hz
  · have : Tendsto (fun z : ℂ => C * ‖z - z0‖) (𝓝 z0) (𝓝 (C * ‖z0 - z0‖)) :=
      (((continuous_id.sub continuous_const).norm).const_mul C).tendsto z0
    simp only [sub_self, norm_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
end FroehlichSpencer.Infra
