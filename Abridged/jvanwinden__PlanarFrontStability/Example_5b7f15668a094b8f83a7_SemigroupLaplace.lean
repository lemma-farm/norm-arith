module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.Semigroup ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
@[expose] public section
/-!
# Strongly continuous semigroups

This file gives a small project-local interface for strongly continuous (`C₀`) semigroups of
continuous linear operators on a Banach space.  Time is `ℝ≥0`; using nonnegative time makes the
semigroup law and its growth consequences available without extending the semigroup to a group.

The main analytic consequence proved here is the standard exponential operator-norm bound.  Strong
continuity first gives pointwise boundedness on compact time intervals, Banach--Steinhaus upgrades
this to a uniform operator-norm bound, and the semigroup law propagates the bound to all times.
-/
open Set
universe u v
noncomputable section
/-- A strongly continuous one-parameter semigroup of continuous linear endomorphisms.

The convention for composition is `S (s + t) = (S s).comp (S t)`.  Since time addition is
commutative, the operators in the family commute as a consequence. -/
structure C0Semigroup (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The operator at time `t`. -/
  toFun : NNReal → E →L[𝕜] E
  /-- The operator at time zero is the identity. -/
  map_zero' : toFun 0 = ContinuousLinearMap.id 𝕜 E
  /-- The semigroup law. -/
  map_add' : ∀ s t, toFun (s + t) = (toFun s).comp (toFun t)
  /-- Every orbit is continuous in time (strong continuity). -/
  strongContinuous' : ∀ x, Continuous fun t ↦ toFun t x
namespace C0Semigroup
variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
instance instFunLike : FunLike (C0Semigroup 𝕜 E) NNReal (E →L[𝕜] E) where
  coe S := S.toFun
  coe_injective S T h := by
    cases S
    cases T
    congr

end C0Semigroup

namespace ContractionSemigroup
variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

end ContractionSemigroup

end
end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.SemigroupGenerator ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The generator relation of a strongly continuous semigroup

The generator is characterized by a right derivative in the ambient Banach norm. The semigroup
law propagates this derivative along each orbit. Integrating the right derivative gives the
usual integral identity and, in turn, two-sided differentiability at positive times.
These facts connect the explicit longitudinal heat construction to the operator in the paper.
-/
open Filter MeasureTheory Set Topology
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
/-- The orbit on real time, extended constantly to negative times. -/
def realOrbit (S : C0Semigroup ℂ E) (x : E) (t : ℝ) : E := S t.toNNReal x

end
end C0Semigroup

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_5b7f15668a094b8f83a7_SemigroupLaplace ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The Laplace resolvent of a strongly continuous semigroup

Integration of an exponentially decaying orbit inverts the negative generator. The closed
generator graph justifies passing from finite orbit integrals to the improper integral.
Complex exponential rescaling then gives the resolvent for `Re z > ω`, with the bound
`M / (Re z - ω)`. These are right-half-plane estimates, not yet sectorial estimates.
-/
open Filter MeasureTheory Set Topology
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
set_option linter.unusedVariables false in
axiom _root_.C0Semigroup.norm_realOrbit_le_of_exp_bound.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E]
  [inst_2 : CompleteSpace E] (S : C0Semigroup ℂ E) {M ω : ℝ},
  (∀ (t : NNReal), ‖(S : NNReal → E →L[ℂ] E) t‖ ≤ M * Real.exp (ω * (↑t : ℝ))) →
    ∀ (x : E) {t : ℝ}, 0 ≤ t → ‖S.realOrbit x t‖ ≤ M * ‖x‖ * Real.exp (ω * t)
theorem norm_integral_realOrbit_le (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤ (M / (-ω)) * ‖x‖ := by
  have hi := (integrableOn_exp_mul_Ioi hω 0).const_mul (M * ‖x‖)
  calc
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤
        ∫ t in Ioi (0 : ℝ), (M * ‖x‖) * Real.exp (ω * t) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact S.norm_realOrbit_le_of_exp_bound hbound x ht.le
    _ = (M / (-ω)) * ‖x‖ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hω]
      simp only [mul_zero, Real.exp_zero]
      ring
end
end C0Semigroup
