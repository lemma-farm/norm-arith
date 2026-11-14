module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Dependencies.v6e3e56a75585.KakeyaTwoScale.NormalProjection ====
public section
@[expose] public section
open Metric
noncomputable section
namespace KakeyaTwoScale
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
/-- Canonical ambient-valued projection normal to H. -/
def normalProjection (H : Submodule ℝ X) [H.HasOrthogonalProjection] : X →L[ℝ] X :=
  Hᗮ.starProjection

variable (H : Submodule ℝ X) [H.HasOrthogonalProjection]

def normalDirection (v : X) : X := ‖normalProjection H v‖⁻¹ • normalProjection H v

end KakeyaTwoScale

end
end
end

-- ==== Examples.mrklwk__kakeya_two_scale_lean.Examples.Example_9718c5b2b0812c6b144b_NormalPlaneNet ====
@[expose] public section
noncomputable section
namespace KakeyaTwoScale
variable {X J : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

set_option linter.unusedVariables false in
/-- Projective proximity gives a signed velocity approximation, with the
normal speed as the exact factor. Both antipodal cases are included. -/
theorem normal_velocity_approximation (H : Submodule ℝ X) [H.HasOrthogonalProjection]
    (v a : X) (epsilon : ℝ) (hv : 0 < ‖normalProjection H v‖)
    (hclose : dist (normalDirection H v) a ≤ epsilon ∨
      dist (normalDirection H v) (-a) ≤ epsilon) 
    (h_KakeyaTwoScale_normalDirection_decomposition : ∀ {X : Type u_1} [inst : NormedAddCommGroup X] [inst_1 : InnerProductSpace ℝ X] (H : Submodule ℝ X)
      [inst_2 : H.HasOrthogonalProjection] {v : X},
      0 < ‖(KakeyaTwoScale.normalProjection H : X → X) v‖ →
        (KakeyaTwoScale.normalProjection H : X → X) v =
          ‖(KakeyaTwoScale.normalProjection H : X → X) v‖ • KakeyaTwoScale.normalDirection H v)
    :
    ∃ c : ℝ, |c| = ‖normalProjection H v‖ ∧
      ‖normalProjection H v-c • a‖ ≤ ‖normalProjection H v‖*epsilon := by
  have step (u : X) (hu : dist (normalDirection H v) u ≤ epsilon) :
      ‖normalProjection H v-‖normalProjection H v‖ • u‖ ≤
        ‖normalProjection H v‖*epsilon := by
    calc
      _ = ‖‖normalProjection H v‖ • (normalDirection H v-u)‖ := by
        congr 1
        rw [smul_sub, ← h_KakeyaTwoScale_normalDirection_decomposition H hv]
      _ = ‖normalProjection H v‖*dist (normalDirection H v) u := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hv, dist_eq_norm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hu hv.le
  rcases hclose with h | h
  · exact ⟨_, abs_of_pos hv, step a h⟩
  · refine ⟨-‖normalProjection H v‖, by simp [abs_of_pos hv], ?_⟩
    simpa using step (-a) h

end KakeyaTwoScale
