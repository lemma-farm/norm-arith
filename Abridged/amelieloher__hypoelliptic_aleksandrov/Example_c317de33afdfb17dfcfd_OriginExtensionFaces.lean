module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.ve2c706b4ba90.HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Literal plane geometry for the homogeneous Bellman problem -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The anisotropic position-velocity dilation on the ambient plane. -/
def bellmanPlaneDilation (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (r ^ 3 * q.1, r * q.2)

end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.ve2c706b4ba90.HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # C² homogeneous functions and their continuous Bellman images -/
@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The open punctured product plane. -/
def bellmanPuncturedSet : Set (ℝ × ℝ) := {q | q ≠ (0, 0)}
end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_c317de33afdfb17dfcfd_OriginExtensionFaces ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The literal kinetic inner rectangle and its normal surface weights -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory
/-- Reference parametrizations of the two position faces and two velocity faces. -/
def bellmanOriginFace (i : Fin 4) (w : ℝ) : ℝ × ℝ :=
  if i.val < 2 then (if i.val = 0 then -1 else 1, w)
  else (w, if i.val = 2 then -1 else 1)

def bellmanOriginFaceError (k : ℕ) (delta : ℝ) (i : Fin 4)
    (f test : (ℝ × ℝ) → ℝ) : ℝ :=
  delta ^ k * ∫ w in (-1 : ℝ)..1,
    f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
      test (bellmanPlaneDilation delta (bellmanOriginFace i w))
set_option linter.unusedVariables false in
theorem bellmanOriginFaceError_bound (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hscale : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i : Fin 4, ∀ w ∈ Icc (-1 : ℝ) 1, |f (bellmanOriginFace i w)| ≤ C)
    (test : (ℝ × ℝ) → ℝ) (M : ℝ) (_hM : 0 ≤ M) (hMt : ∀ q, |test q| ≤ M)
    (k : ℕ) (delta : ℝ) (hd : 0 < delta) (i : Fin 4) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_bellmanOriginFace_ne_zero : ∀ (i : Fin 4) (w : ℝ), HypoellipticAleksandrov.KineticAleksandrov.bellmanOriginFace i w ≠ (0, 0))
    :
    |bellmanOriginFaceError k delta i f test| ≤ 2 * C * M * delta ^ (beta + k) := by
  have hi : |∫ w in (-1 : ℝ)..1,
      f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
      (delta ^ beta * C * M) * 2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := delta ^ beta * C * M)
      (f := fun w => f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))) (fun w hw => ?_)
    · simpa only [Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two, abs_of_pos
        (by norm_num : (0 : ℝ) < 2)] using hh
    · have hw' : -1 < w ∧ w ≤ 1 := by simpa using hw
      rw [Real.norm_eq_abs, abs_mul,
        hscale delta hd _ (h_HypoellipticAleksandrov_KineticAleksandrov_bellmanOriginFace_ne_zero i w), abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hd beta)]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb i w ⟨hw'.1.le, hw'.2⟩)
          (Real.rpow_nonneg hd.le _)
      · exact hMt _
      · exact abs_nonneg _
      · exact mul_nonneg (Real.rpow_nonneg hd.le _) hC
  unfold bellmanOriginFaceError
  rw [abs_mul, abs_of_nonneg (pow_nonneg hd.le k)]
  calc
    delta ^ k * |∫ w in (-1 : ℝ)..1,
        f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
          test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
        delta ^ k * ((delta ^ beta * C * M) * 2) :=
      mul_le_mul_of_nonneg_left hi (pow_nonneg hd.le k)
    _ = 2 * C * M * delta ^ (beta + k) := by
      rw [Real.rpow_add hd, Real.rpow_natCast]
      ring
end HypoellipticAleksandrov.KineticAleksandrov
