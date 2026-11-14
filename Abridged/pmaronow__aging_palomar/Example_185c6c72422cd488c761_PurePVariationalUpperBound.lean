module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.pmaronow__aging_palomar.Dependencies.ve8ca621996be.SphericalAging.ExternalFieldElementaryPenalty ====
public section
set_option autoImplicit false
public section
/-! A genuine all-p external-field opening inequality. The literal published
field ceiling is evaluated at an explicit field depending on overlap. This
yields a strictly positive polynomial penalty for every p≥3. It is a weaker
coefficient than source 10.2's sharp beta_d and does not assert a stochastic
algorithmic threshold or overlap-cost conclusion. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.ExternalFieldElementaryPenalty

@[expose]  def thresholdEnergy (p : ℕ) : ℝ := 2*Real.sqrt (((p:ℝ)-1)/(p:ℝ))

@[expose]  def fieldOrder (p : ℕ) (κ : ℝ) : ℝ := (κ^2/((p:ℝ)*((p:ℝ)-2)))^(1/((p:ℝ)-1))
@[expose]  def algorithmicField (p : ℕ) (κ : ℝ) : ℝ :=
  if κ^2≤(p:ℝ)*((p:ℝ)-2) then
    thresholdEnergy p+((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*
      fieldOrder p κ^((p:ℝ)/2)
  else Real.sqrt ((p:ℝ)+κ^2)

 
 
 
 
end SphericalAging.ExternalFieldElementaryPenalty

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.ve8ca621996be.SphericalAging.PurePBranchingVariationalBound ====
public section
set_option autoImplicit false
public section
/-! The literal pure-p deterministic branching functional. Actual admissible
correlation schedules are compared with the fully correlated schedule, and
its finite sums are bounded by a continuum integral plus an explicit mesh error.
The Gaussian small-increment estimate is a separate preceding ingredient. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace SphericalAging.PurePBranchingVariationalBound

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] def prime (p : ℕ) (x : ℝ) : ℝ := (p:ℝ)*x^(p-1)

end SphericalAging.PurePBranchingVariationalBound

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.ve8ca621996be.SphericalAging.PurePFieldObstacle ====
public section
set_option autoImplicit false
public section
/-! The actual low-field pure-p obstacle: a matching straight line below t
and κ²+ξ' above t, where κ²=p(p−2)t^(p−1). Its dual slopes and the cumulative
comparison are proved directly from the monomial. -/
noncomputable section
open Set
open scoped BigOperators
namespace SphericalAging.PurePFieldObstacle
open  PurePBranchingVariationalBound

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] def fieldSquared (p : ℕ) (t : ℝ) : ℝ := (p:ℝ)*((p:ℝ)-2)*t^(p-1)

end SphericalAging.PurePFieldObstacle

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.ve8ca621996be.SphericalAging.PurePFieldContinuumProfile ====
public section
set_option autoImplicit false
public section
/-! The genuine low-field matching profile has the exact printed ALG value.
Its finite obstacle sums have an explicit vanishing mesh error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalAging.PurePFieldContinuumProfile
open   PurePBranchingVariationalBound
open  PurePFieldObstacle ExternalFieldElementaryPenalty
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[expose] def lowFieldValue (p : ℕ) (t : ℝ) : ℝ := thresholdEnergy p+
  ((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*t^((p:ℝ)/2)

end SphericalAging.PurePFieldContinuumProfile

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.ve8ca621996be.SphericalAging.SqrtMassIntegralPartition ====
public section
set_option autoImplicit false
public section
/-! A genuine integrable nonnegative density is compared with its actual
cumulative-mass finite sums by interval Cauchy--Schwarz. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SphericalAging.SqrtMassIntegralPartition

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] def mass (a : ℝ→ℝ) (x : ℝ) : ℝ := ∫y in (0:ℝ)..x,a y

end SphericalAging.SqrtMassIntegralPartition

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Examples.Example_185c6c72422cd488c761_PurePVariationalUpperBound ====
set_option autoImplicit false
public section
/-! The literal single-species pure-p variational functional is bounded by
the printed piecewise ALG_p(κ). Its cumulative obstacle is derived from the
actual field density and the admissible correlation cumulative function. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.PurePVariationalUpperBound
open PurePBranchingVariationalBound PurePFieldObstacle PurePFieldContinuumProfile
open  SqrtMassIntegralPartition ExternalFieldElementaryPenalty
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false


set_option linter.unusedVariables false in
theorem integral_sqrt_le_algorithmicField {p : ℕ} (hp : 3≤p) {κ : ℝ} (hκ : 0≤κ)
    (a : ℝ→ℝ) (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x)
    (hs : IntervalIntegrable (fun x => Real.sqrt (a x)) volume 0 1)
    (hcap : ∀x∈Icc 0 1,mass a x≤κ^2+prime p x) 
    (h_SphericalAging_PurePVariationalUpperBound_fieldOrder_mem : ∀ {p : ℕ},
      3 ≤ p →
        ∀ {κ : ℝ},
          κ ^ 2 ≤ (↑p : ℝ) * ((↑p : ℝ) - 2) →
            SphericalAging.ExternalFieldElementaryPenalty.fieldOrder p κ ∈ Set.Icc 0 1)
    (h_SphericalAging_PurePFieldContinuumProfile_lowFieldValue_eq_algorithmicField : ∀ {p : ℕ},
      3 ≤ p →
        ∀ {t : ℝ},
          t ∈ Set.Icc 0 1 →
            SphericalAging.PurePFieldContinuumProfile.lowFieldValue p t =
              SphericalAging.ExternalFieldElementaryPenalty.algorithmicField p
                √(SphericalAging.PurePFieldObstacle.fieldSquared p t))
    (h_SphericalAging_ResponseTransport_interval_square_bound : ∀ {u v : ℝ} {f : ℝ → ℝ},
      u < v →
        IntervalIntegrable f MeasureTheory.MeasureSpace.volume u v →
          IntervalIntegrable (fun (s : ℝ) ↦ f s ^ 2) MeasureTheory.MeasureSpace.volume u v →
            (∫ (s : ℝ) in u..v, f s) ^ 2 ≤ (v - u) * ∫ (s : ℝ) in u..v, f s ^ 2)
    (h_SphericalAging_ExternalFieldSharpScalar_algorithmicField_high : ∀ {p : ℕ},
      3 ≤ p →
        ∀ {κ : ℝ},
          (↑p : ℝ) * ((↑p : ℝ) - 2) ≤ κ ^ 2 →
            SphericalAging.ExternalFieldElementaryPenalty.algorithmicField p κ = √((↑p : ℝ) + κ ^ 2))
    (h_SphericalAging_PurePObstacleIntegralBound_integral_sqrt_le_lowFieldValue : ∀ {p : ℕ},
      3 ≤ p →
        ∀ (a : ℝ → ℝ),
          IntervalIntegrable a MeasureTheory.MeasureSpace.volume 0 1 →
            (∀ x ∈ Set.Icc 0 1, 0 ≤ a x) →
              IntervalIntegrable (fun (x : ℝ) ↦ √(a x)) MeasureTheory.MeasureSpace.volume 0 1 →
                ∀ {κ t : ℝ},
                  t ∈ Set.Icc 0 1 →
                    κ ^ 2 ≤ SphericalAging.PurePFieldObstacle.fieldSquared p t →
                      (∀ x ∈ Set.Icc 0 1,
                          SphericalAging.SqrtMassIntegralPartition.mass a x ≤
                            κ ^ 2 + SphericalAging.PurePBranchingVariationalBound.prime p x) →
                        ∫ (x : ℝ) in 0..1, √(a x) ≤
                          SphericalAging.PurePFieldContinuumProfile.lowFieldValue p t)
    (h_SphericalAging_PurePVariationalUpperBound_fieldSquared_fieldOrder : ∀ {p : ℕ},
      3 ≤ p →
        ∀ (κ : ℝ),
          SphericalAging.PurePFieldObstacle.fieldSquared p
              (SphericalAging.ExternalFieldElementaryPenalty.fieldOrder p κ) =
            κ ^ 2)
    :
    (∫x in (0:ℝ)..1,Real.sqrt (a x))≤algorithmicField p κ := by
  by_cases hlow : κ^2≤(p:ℝ)*((p:ℝ)-2)
  · have ht := h_SphericalAging_PurePVariationalUpperBound_fieldOrder_mem hp hlow
    have h := h_SphericalAging_PurePObstacleIntegralBound_integral_sqrt_le_lowFieldValue hp a ha han hs ht
      (by rw [h_SphericalAging_PurePVariationalUpperBound_fieldSquared_fieldOrder hp]) hcap
    rw [h_SphericalAging_PurePFieldContinuumProfile_lowFieldValue_eq_algorithmicField hp ht,h_SphericalAging_PurePVariationalUpperBound_fieldSquared_fieldOrder hp,Real.sqrt_sq hκ] at h
    exact h
  · have hs2 : IntervalIntegrable (fun x => Real.sqrt (a x)^2) volume 0 1 := by
      apply ha.congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact (Real.sq_sqrt (han x ⟨hx.1.le,hx.2⟩)).symm
    have hsq := h_SphericalAging_ResponseTransport_interval_square_bound (by norm_num : (0:ℝ)<1) hs hs2
    have he : (∫x in (0:ℝ)..1,Real.sqrt (a x)^2)=mass a 1 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact Real.sq_sqrt (han x hx)
    rw [he,sub_zero,one_mul] at hsq
    have hm := hcap 1 (by norm_num)
    simp only [prime,one_pow,mul_one] at hm
    rw [h_SphericalAging_ExternalFieldSharpScalar_algorithmicField_high hp (le_of_not_ge hlow)]
    apply Real.le_sqrt_of_sq_le
    linarith

end SphericalAging.PurePVariationalUpperBound
