module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v55d5f3362286.RothschildStein.H2.LocalizedKernelDefs ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
/-- A [0,1]-valued Lipschitz cutoff which vanishes outside U.
BB Definition 7.9, p. 299. -/
structure KernelCutoff (U : Set X) (L : ℝ≥0) (a : X → ℝ) : Prop where
  lipschitz : LipschitzWith L a
  nonneg : ∀ x, 0 ≤ a x
  le_one : ∀ x, a x ≤ 1
  outside : ∀ x, x ∉ U → a x = 0

end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v55d5f3362286.RothschildStein.H2.HolderSpaces ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]
/-- Hölder seminorm on a set, using Mathlib's least Hölder constant.
BB Definition 7.6, p. 298. An infinite value records failure of Hölder boundedness. -/
def holderSemi (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  eHolderNorm δ (fun x : A => f x)

end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_026d136d770613a39350_CutoffHolderBounds ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]
set_option linter.unusedVariables false in
/-- The explicit cutoff seminorm bound on a ball, using its diameter
bound 2r rather than any special metric-ball diameter equality. BB p. 308. -/
theorem KernelCutoff.holderSemi_ball_le {U : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) {z : X} {r : ℝ} (hr : 0 < r)
    {γ : ℝ≥0} (hγ : γ ≤ 1) 
    (h_RothschildStein_H2_dist_lt_two_radius : ∀ {X : Type u_1} [inst : MetricSpace X] {z x y : X} {R : ℝ},
      x ∈ Metric.ball z R → y ∈ Metric.ball z R → Dist.dist x y < 2 * R)
    (h_RothschildStein_H2_holderSemi_le_of_bound : ∀ {X : Type u_1} [inst : MetricSpace X] {δ : NNReal} {A : Set X} {f : X → ℝ} {H : ℝ},
      0 ≤ H →
        (∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ H * Dist.dist x y ^ (↑δ : ℝ)) →
          RothschildStein.H2.holderSemi δ A f ≤ ENNReal.ofReal H)
    (h_RothschildStein_H2_rpow_gain_le : ∀ {t k α ν : ℝ}, 0 < t → t ≤ k → α ≤ ν → t ^ ν ≤ k ^ (ν - α) * t ^ α)
    :
    holderSemi γ (ball z r) b ≤ ENNReal.ofReal ((L : ℝ) * (2 * r) ^ (1 - (γ : ℝ))) := by
  apply h_RothschildStein_H2_holderSemi_le_of_bound (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (by linarith) _))
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, abs_zero, dist_self]
    exact mul_nonneg (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by norm_num) _)
  have hd := dist_pos.mpr hxy
  have hp := h_RothschildStein_H2_rpow_gain_le (α := (γ : ℝ)) (ν := 1) hd (h_RothschildStein_H2_dist_lt_two_radius hx hy).le (show (γ : ℝ) ≤ 1 from hγ)
  rw [Real.rpow_one] at hp
  have he := hb.lipschitz.dist_le_mul x y
  rw [Real.dist_eq] at he
  have he' := mul_le_mul_of_nonneg_left hp L.coe_nonneg
  nlinarith

end RothschildStein.H2
