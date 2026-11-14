module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.Compact
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

-- ==== Examples.scottnarmstrong__SuperdiffusionCLT.Dependencies.v4e0c43d2d289.Homogenization.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__SuperdiffusionCLT.Dependencies.v4e0c43d2d289.SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas ====
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
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The uniform `C^{1,1}` atlas of a smooth bounded domain

* `Section7.HasC11ChartAt`, `Section7.IsUniformC11Domain`: the quantitative `C^{1,1}` charts.
* `Section7.exists_isUniformC11Domain_of_isSmoothBoundedDomain`: a smooth bounded domain is
  uniformly `C^{1,1}`. The charts of `IsSmoothBoundedDomain` are globalized by a bump function
  (so the slope and gradient-Lipschitz bounds hold on the whole space), and finitely many charts
  cover the compact frontier.
-/
@[expose] public section
namespace SuperdiffusionCLT.Section7
open Homogenization
variable {d : ℕ}
/-- Quantitative `C^{1,1}` chart at a boundary point: a smooth graph function (globalized by a
cutoff) with slope bound `M₁` and gradient-Lipschitz bound `M₂`, describing `U` on `B(x,r)`. -/
def HasC11ChartAt (U : Set (Vec d)) (x : Vec d) (r M₁ M₂ : ℝ) : Prop :=
  ∃ (e : Vec d) (ψ : Vec d → ℝ), vecNormSq e = 1 ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
    (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) ∧
    (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) ∧
    ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))

set_option linter.unusedVariables false in
axiom _root_.SuperdiffusionCLT.Section7.HasC11ChartAt.mono : ∀ {d : ℕ} {U : Set (Homogenization.Vec d)} {x : Homogenization.Vec d} {r r' M₁ M₂ M₁' M₂' : ℝ},
  SuperdiffusionCLT.Section7.HasC11ChartAt U x r M₁ M₂ →
    r' ≤ r → M₁ ≤ M₁' → M₂ ≤ M₂' → SuperdiffusionCLT.Section7.HasC11ChartAt U x r' M₁' M₂'

end SuperdiffusionCLT.Section7

end
end

-- ==== Examples.scottnarmstrong__SuperdiffusionCLT.Dependencies.v4e0c43d2d289.SuperdiffusionCLT.Section7.Analytic.Change.Shear ====
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
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The coordinate shear

For a unit vector `e` and a function `ψ`, the shear `y ↦ y - ψ(Py) e`, with `P y = y - ⟨e,y⟩ e`
the orthogonal projection onto `e^⊥`, preserves Lebesgue measure and has the explicit inverse
`y ↦ y + ψ(Py) e`.

## Main results

* `Section7.shear`
* `Section7.shear_neg_left_inverse`, `Section7.shear_neg_right_inverse`
* `Section7.measurePreserving_shear`
-/
@[expose] public section
open MeasureTheory Homogenization
namespace SuperdiffusionCLT.Section7
variable {d : ℕ}
/-- The shear `y ↦ y - ψ(Py) e` along the unit vector `e`, `P y = y - ⟨e,y⟩ e`. -/
noncomputable def shear (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) : Vec d :=
  y - ψ (y - vecDot e y • e) • e

end SuperdiffusionCLT.Section7

end
end

-- ==== Examples.scottnarmstrong__SuperdiffusionCLT.Dependencies.v4e0c43d2d289.SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform ====
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
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Affine changes of variables and chart estimates for uniformly `C^{1,1}` domains

* `Section7.IsUniformC11Domain.affineImage`: the image of a uniformly `C^{1,1}` domain under
  `x ↦ λ x + z` (`λ > 0`) has data `(λ r, M₁, M₂ / λ, λ D)`.
* `Section7.IsUniformC11Domain.translate`, `Section7.IsUniformC11Domain.smul`: the two special
  cases (translation keeps all four parameters; dilation by `λ` gives `(λ r, M₁, M₂/λ, λ D)`).
* chart estimates: Lipschitz bounds for the graph projection `y ↦ y - ⟨e, y⟩ e`, for the
  graph function `ψ` and for the shear `y ↦ y - ψ(Py) e` and its inverse; frontier points of `U`
  inside a chart ball lie on the graph; the vertical distance of a point of `U` to the graph is
  at most a constant times its distance to any frontier point in the chart ball.
-/
@[expose] public section
namespace SuperdiffusionCLT.Section7
open Homogenization Pointwise
variable {d : ℕ}
/-! ### Affine images -/

set_option linter.unusedVariables false in
axiom _root_.SuperdiffusionCLT.Section7.HasC11ChartAt.affine : ∀ {d : ℕ} {U : Set (Homogenization.Vec d)} {x : Homogenization.Vec d} {r M₁ M₂ : ℝ},
  SuperdiffusionCLT.Section7.HasC11ChartAt U x r M₁ M₂ →
    ∀ {l : ℝ},
      0 < l →
        ∀ (z : Homogenization.Vec d),
          SuperdiffusionCLT.Section7.HasC11ChartAt
            ((fun (y : Homogenization.Vec d) ↦ l • y + z) '' U) (l • x + z) (l * r) M₁ (M₂ / l)

/-! ### Chart estimates -/

end SuperdiffusionCLT.Section7

end
end

-- ==== Examples.scottnarmstrong__SuperdiffusionCLT.Examples.Example_38742ad6e5534816f907_BoundaryRoundedB ====
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
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The shear preimage of a uniformly `C^{1,1}` domain

* `Section7.g1b_hasC11ChartAt_congr`: charts only see the set on a ball.
* `Section7.g1b_isUniformC11Domain_shear_preimage`: if the frontier charts of `H` over the
  cylinder `‖P y‖ < ρ + δ` have direction `±e`, and `Ψ` is constant for `‖w‖ ≥ ρ`, then
  `{y | shear e Ψ y ∈ H}` is a uniformly `C^{1,1}` domain.
-/
@[expose] public section
namespace SuperdiffusionCLT.Section7
open Homogenization
variable {d : ℕ}

set_option linter.unusedVariables false in
/-- Away from the cylinder where `Ψ` varies, the shear is a translation and charts translate. -/
theorem g1b_chart_shear_far {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ} {c ρ δ : ℝ}
    (hΨc : ∀ w, ρ ≤ ‖w‖ → Ψ w = c) (hδ : 0 < δ) {H : Set (Vec d)} {p : Vec d}
    {r M₁ M₂ : ℝ} (hp : ρ + δ ≤ ‖p - vecDot e p • e‖)
    (h : HasC11ChartAt H (shear e Ψ p) r M₁ M₂) 
    (h_SuperdiffusionCLT_Section7_g1b_hasC11ChartAt_congr : ∀ {d : ℕ} {U U' : Set (Homogenization.Vec d)} {x : Homogenization.Vec d} {r ρ M₁ M₂ : ℝ},
      SuperdiffusionCLT.Section7.HasC11ChartAt U x r M₁ M₂ →
        (∀ y ∈ Metric.ball x ρ, y ∈ U ↔ y ∈ U') →
          SuperdiffusionCLT.Section7.HasC11ChartAt U' x (Min.min r ρ) M₁ M₂)
    (h_SuperdiffusionCLT_Section7_norm_proj_sub_le : ∀ {d : ℕ} {e : Homogenization.Vec d},
      Homogenization.vecNormSq e = 1 →
        ∀ (y z : Homogenization.Vec d),
          ‖y - Homogenization.vecDot e y • e - (z - Homogenization.vecDot e z • e)‖ ≤
            (1 + (↑d : ℝ)) * ‖y - z‖)
    :
    HasC11ChartAt {y | shear e Ψ y ∈ H} p (min r (δ / (1 + d))) M₁ M₂ := by
  have hpc : Ψ (p - vecDot e p • e) = c := hΨc _ (by linarith only [hp, hδ])
  have hq : shear e Ψ p = p - c • e := by unfold shear; rw [hpc]
  have h1 := h.affine (l := 1) one_pos (c • e)
  rw [hq, one_smul, sub_add_cancel] at h1
  have hd : (0 : ℝ) < 1 + d := by positivity
  refine (h_SuperdiffusionCLT_Section7_g1b_hasC11ChartAt_congr (ρ := δ / (1 + d)) h1 ?_).mono (by rw [one_mul]) le_rfl
    (by rw [div_one])
  intro y hy
  have hyc : Ψ (y - vecDot e y • e) = c := by
    refine hΨc _ ?_
    have h2 := h_SuperdiffusionCLT_Section7_norm_proj_sub_le he y p
    have h3 : ‖y - p‖ < δ / (1 + d) := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h4 : (1 + d) * ‖y - p‖ < δ := by
      have := (lt_div_iff₀ hd).1 h3
      linarith only [this]
    have h5 := norm_sub_norm_le (p - vecDot e p • e) (y - vecDot e y • e)
    have h6 := norm_sub_rev (p - vecDot e p • e) (y - vecDot e y • e)
    linarith only [h2, h4, h5, h6, hp]
  have hshear : shear e Ψ y = y - c • e := by unfold shear; rw [hyc]
  show y ∈ (fun y => (1 : ℝ) • y + c • e) '' H ↔ shear e Ψ y ∈ H
  rw [hshear]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y - c • e := by rw [← hzy]; simp
    rw [← this]
    exact hz
  · intro hH
    exact ⟨y - c • e, hH, by simp⟩
end SuperdiffusionCLT.Section7
