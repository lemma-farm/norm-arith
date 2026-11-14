module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.LocDoubling ====
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
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
/-- The fixed locally doubling data, with finite outer measure recorded explicitly (BB Definition 7.1, p. 295). -/
structure LocDoubling (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  μ : Measure X
  Ω₀ : Set X
  Ω₁ : Set X
  Ω₂ : Set X
  open₀ : IsOpen Ω₀
  open₁ : IsOpen Ω₁
  open₂ : IsOpen Ω₂
  sub₀₁ : Ω₀ ⊆ Ω₁
  sub₁₂ : Ω₁ ⊆ Ω₂
  cpt : IsCompact (closure Ω₂)
  κ : ℝ
  κ_pos : 0 < κ
  incl₀ : ∀ y ∈ Ω₀, closedBall y (6 * κ) ⊆ Ω₁
  incl₁ : ∀ y ∈ Ω₁, closedBall y (6 * κ) ⊆ Ω₂
  C_D : ℝ
  one_lt_C_D : 1 < C_D
  doubling : ∀ x ∈ Ω₁, ∀ r : ℝ, 0 < r → r ≤ 3 * κ →
    0 < μ (ball x (2 * r)) ∧
      μ (ball x (2 * r)) ≤ ENNReal.ofReal C_D * μ (ball x r) ∧
      μ (ball x r) < ⊤
  noAtoms : ∀ x : X, μ {x} = 0
  finΩ₂ : μ Ω₂ < ⊤

/-- A doubling patch (P1–P5), including finite outer measure, compact centre
closure and absence of atoms. The parameter sets need not be open. -/
structure DoublingPatch (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  μ : Measure X
  S : Set X
  W : Set X
  ρ : ℝ
  C_D : ℝ
  ρ_pos : 0 < ρ
  one_lt_C_D : 1 < C_D
  incl : ∀ z ∈ S, ball z (6 * ρ) ⊆ W
  doubling : ∀ z ∈ S, ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
    0 < μ (ball z s) ∧ μ (ball z s) < ⊤ ∧
      μ (ball z s) ≤ ENNReal.ofReal C_D * μ (ball z (s / 2))
  measurable_W : MeasurableSet W
  finite_W : μ W < ⊤
  compact_closure : IsCompact (closure S)
  noAtoms : ∀ x : X, μ {x} = 0
/-- The volume function used away from the diagonal (BB p. 295).
Its total extension has value zero on the diagonal; kernels exclude that null point. -/
def volumeAt {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x y : X) : ℝ≥0∞ := μ (ball x (dist x y))
end RothschildStein.H2

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.Patches ====
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
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
set_option linter.unusedVariables false in
axiom _root_.RothschildStein.H2.LocDoubling.doubling_half.{w_u_1} : ∀ {X : Type w_u_1} [inst : MetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X]
  (D : RothschildStein.H2.LocDoubling X) {z : X},
  z ∈ D.Ω₁ →
    ∀ {s : ℝ},
      0 < s →
        s ≤ 6 * D.κ →
          0 < (D.μ : Set X → ENNReal) (Metric.ball z s) ∧
            (D.μ : Set X → ENNReal) (Metric.ball z s) < ⊤ ∧
              (D.μ : Set X → ENNReal) (Metric.ball z s) ≤
                ENNReal.ofReal D.C_D * (D.μ : Set X → ENNReal) (Metric.ball z (s / 2))
/-- The outer patch (Ω₁, Ω₂, κ, C_D). -/
def LocDoubling.outerPatch (D : LocDoubling X) : DoublingPatch X where
  μ := D.μ
  S := D.Ω₁
  W := D.Ω₂
  ρ := D.κ
  C_D := D.C_D
  ρ_pos := D.κ_pos
  one_lt_C_D := D.one_lt_C_D
  incl := fun z hz => ball_subset_closedBall.trans (D.incl₁ z hz)
  doubling := fun _z hz _ hs hκ => D.doubling_half hz hs hκ
  measurable_W := D.open₂.measurableSet
  finite_W := D.finΩ₂
  compact_closure := D.cpt.of_isClosed_subset isClosed_closure (closure_mono D.sub₁₂)
  noAtoms := D.noAtoms
end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.KernelClass ====
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
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
/-- The radial weight d(x,y)^ν / V(x;y) from BB (7.6), p. 299.
The total extension is used only off the diagonal in the kernel bounds. -/
def kernelWeight (μ : Measure X) (ν : ℝ) (x y : X) : ℝ :=
  dist x y ^ ν / (volumeAt μ x y).toReal
/-- The two estimates of BB Definition 7.10, p. 299. Smoothness is in the
first variable only. Measurability is on E × E, with no restriction outside E. -/
structure KernelClass (μ : Measure X) (E : Set X) (β ν A S : ℝ)
    (K : X → X → ℝ) : Prop where
  measurable_E : MeasurableSet E
  measurable : Measurable (fun p : E × E => K p.1 p.2)
  β_pos : 0 < β
  β_le_one : β ≤ 1
  ν_nonneg : 0 ≤ ν
  A_nonneg : 0 ≤ A
  S_nonneg : 0 ≤ S
  size : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → |K x y| ≤ A * kernelWeight μ ν x y
  smooth : ∀ x₀ ∈ E, ∀ x ∈ E, ∀ y ∈ E, 2 * dist x₀ x < dist x₀ y →
    |K x₀ y - K x y| ≤ S * kernelWeight μ ν x₀ y * (dist x₀ x / dist x₀ y) ^ β

end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.VolumeIntegrals ====
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
open scoped ENNReal
namespace RothschildStein.H2
/-- The explicit geometric-series constant in BB Lemma 7.5, p. 297. -/
def volumeIntegralConstant (C β : ℝ) : ℝ := C / (1 - (2 : ℝ) ^ (-β))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.ScaledTail ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
set_option linter.unusedVariables false in
axiom _root_.RothschildStein.H2.DoublingPatch.scaled_outer_volume_integral.{w_u_1} : ∀ {X : Type w_u_1} [inst : MetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X]
  (P : RothschildStein.H2.DoublingPatch X) {z : X},
  z ∈ P.S →
    ∀ {β r σ : ℝ},
      0 < β →
        0 < r →
          4 * r ≤ σ →
            σ ≤ 6 * P.ρ →
              ENNReal.ofReal (r ^ β) *
                  ∫⁻ (y : X) in Metric.ball z σ \ Metric.ball z (4 * r),
                    ENNReal.ofReal (Dist.dist z y ^ (-β)) *
                      (RothschildStein.H2.volumeAt P.μ z y)⁻¹ ∂P.μ ≤
                ENNReal.ofReal (RothschildStein.H2.volumeIntegralConstant P.C_D β * 4 ^ (-β))
end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.KernelTailBound ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
set_option linter.unusedVariables false in
axiom _root_.RothschildStein.H2.DoublingPatch.transpose_difference_enorm.{w_u_1} : ∀ {X : Type w_u_1} [inst : MetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X]
  (P : RothschildStein.H2.DoublingPatch X) {E : Set X} {β A S r : ℝ} {K : X → X → ℝ},
  (RothschildStein.H2.KernelClass P.μ E β 0 A S fun (x y : X) ↦ K y x) →
    ∀ {z x y : X},
      z ∈ P.S →
        z ∈ E →
          x ∈ E →
            y ∈ E →
              0 < r →
                Dist.dist z x < r →
                  4 * r ≤ Dist.dist z y →
                    Dist.dist z y ≤ 6 * P.ρ →
                      ‖K y x - K y z‖ₑ ≤
                        ENNReal.ofReal S * ENNReal.ofReal (r ^ β) *
                          (ENNReal.ofReal (Dist.dist z y ^ (-β)) *
                            (RothschildStein.H2.volumeAt P.μ z y)⁻¹)
end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_91607bf7b5a9433b920c_KernelDifferenceIntegral ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
set_option linter.unusedVariables false in
/-- Uniform L¹ tail of a second-variable kernel difference,
using the transposed smoothness constant and factor 4⁻ᵝ (BB p. 320). -/
theorem LocDoubling.kernel_difference_integral (D : LocDoubling X)
    {xbar z x : X} {R r β A S : ℝ} {K : X → X → ℝ}
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hz : z ∈ D.Ω₁) (hx : x ∈ D.Ω₁)
    (hr : 0 < r) (hcap : 5 * r ≤ D.κ) (hxr : dist z x < r)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0) 
    (h_RothschildStein_H2_kernel_difference_distance_bound : ∀ {X : Type u_1} [inst : MetricSpace X] {K : X → X → ℝ} {xbar z x y : X} {R κ r : ℝ},
      R < κ →
        r ≤ κ / 5 →
          Dist.dist z x < r →
            (∀ (a b : X), a ∉ Metric.ball xbar R ∨ b ∉ Metric.ball xbar R → K a b = 0) →
              K y x - K y z ≠ 0 → Dist.dist z y < 3 * κ)
    (h_RothschildStein_H2_measurable_volumeAt : ∀ {X : Type u_1} [inst : MetricSpace X] [inst_1 : MeasurableSpace X] [BorelSpace X]
      (μ : MeasureTheory.Measure X) (z : X), Measurable (RothschildStein.H2.volumeAt μ z))
    :
    (∫⁻ y in ball xbar R \ ball z (4 * r), ‖K y x - K y z‖ₑ ∂D.μ) ≤
      ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) := by
  let E := ball z (3 * D.κ) \ ball z (4 * r)
  let w : X → ℝ≥0∞ := fun y => ENNReal.ofReal (dist z y ^ (-β)) * (volumeAt D.μ z y)⁻¹
  let c := ENNReal.ofReal S * ENNReal.ofReal (r ^ β)
  have he3 : MeasurableSet (ball z (3 * D.κ)) := isOpen_ball.measurableSet
  have he4 : MeasurableSet (ball z (4 * r)) := isOpen_ball.measurableSet
  have hu : MeasurableSet (ball xbar R) := isOpen_ball.measurableSet
  have hE : MeasurableSet E := he3.diff he4
  have hw : Measurable w :=
    (((continuous_const.dist continuous_id).measurable.pow_const (-β)).ennreal_ofReal).mul
      (h_RothschildStein_H2_measurable_volumeAt D.μ z).inv
  have hbound : ∀ y ∈ ball xbar R \ ball z (4 * r),
      ‖K y x - K y z‖ₑ ≤ c * E.indicator w y := by
    intro y hy
    by_cases he : y ∈ E
    · rw [indicator_of_mem he]
      have hy₁ : y ∈ D.Ω₁ := hU hy.1
      have hd : dist z y ≤ 6 * D.κ := by
        have hh : dist z y < 3 * D.κ := by simpa only [mem_ball, dist_comm] using he.1
        linarith [D.κ_pos]
      have hyr : 4 * r ≤ dist z y := by simpa only [mem_ball, dist_comm, not_lt] using hy.2
      exact D.outerPatch.transpose_difference_enorm hKt hz hz hx hy₁ hr hxr hyr hd
    · have hz0 : K y x - K y z = 0 := by
        by_contra hn
        have hh := h_RothschildStein_H2_kernel_difference_distance_bound hR (by linarith : r ≤ D.κ / 5) hxr hsupport hn
        exact he ⟨by simpa only [mem_ball, dist_comm] using hh, hy.2⟩
      rw [hz0, enorm_zero]
      exact zero_le
  calc
    _ ≤ ∫⁻ y in ball xbar R \ ball z (4 * r), c * E.indicator w y ∂D.μ :=
      setLIntegral_mono' (hu.diff he4) hbound
    _ ≤ ∫⁻ y, c * E.indicator w y ∂D.μ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = c * ∫⁻ y in E, w y ∂D.μ := by
      rw [lintegral_const_mul'' c (hw.indicator hE).aemeasurable, lintegral_indicator hE]
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal (volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (D.outerPatch.scaled_outer_volume_integral hz hKt.β_pos hr
        (by linarith [D.κ_pos]) (by change 3 * D.κ ≤ 6 * D.κ; linarith [D.κ_pos]))
    _ = _ := by rw [← ENNReal.ofReal_mul hKt.S_nonneg]; congr 1; ring
end RothschildStein.H2
