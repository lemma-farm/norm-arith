module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.va1ded437153c.Planarwave.Analysis.Semigroup ====
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

set_option linter.unusedVariables false in
axiom _root_.C0Semigroup.zero_apply.{w_u,w_v} : ∀ {𝕜 : Type w_u} {E : Type w_v} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] [inst_3 : CompleteSpace E] (S : C0Semigroup 𝕜 E) (x : E),
  ((S : NNReal → E →L[𝕜] E) 0 : E → E) x = x
set_option linter.unusedVariables false in
axiom _root_.C0Semigroup.add_apply.{w_u,w_v} : ∀ {𝕜 : Type w_u} {E : Type w_v} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] [inst_3 : CompleteSpace E] (S : C0Semigroup 𝕜 E) (s t : NNReal)
  (x : E),
  ((S : NNReal → E →L[𝕜] E) (s + t) : E → E) x =
    ((S : NNReal → E →L[𝕜] E) s : E → E) (((S : NNReal → E →L[𝕜] E) t : E → E) x)

set_option linter.unusedVariables false in
axiom _root_.C0Semigroup.strongContinuous.{w_u,w_v} : ∀ {𝕜 : Type w_u} {E : Type w_v} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] [inst_3 : CompleteSpace E] (S : C0Semigroup 𝕜 E) (x : E),
  Continuous fun (t : NNReal) ↦ ((S : NNReal → E →L[𝕜] E) t : E → E) x

end C0Semigroup

namespace ContractionSemigroup
variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

end ContractionSemigroup

end
end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_e2fc928f30beeb362bd1_SemigroupOperations ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
@[expose] public section
/-!
# Operations on strongly continuous semigroups

This file provides the two constructions used in the diagonal-diffusion step of Lemma 2.2:
multiplication by a real exponential and finite coordinatewise products.
-/
open scoped NNReal
noncomputable section
namespace C0Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
section Conjugate
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

end Conjugate

section Pi
variable {ι : Type*} [Fintype ι]
  {X : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
  [∀ i, CompleteSpace (X i)]
/-- Finite coordinatewise product of strongly continuous semigroups. -/
def pi (S : ∀ i, C0Semigroup ℂ (X i)) : C0Semigroup ℂ (∀ i, X i) where
  toFun t := ContinuousLinearMap.piMap fun i ↦ S i t
  map_zero' := by
    ext x i
    exact (S i).zero_apply (x i)
  map_add' s t := by
    ext x i
    exact (S i).add_apply s t (x i)
  strongContinuous' x := by
    exact continuous_pi fun i ↦ (S i).strongContinuous (x i)

/-- A common coordinatewise operator-norm bound also bounds the finite product semigroup. -/
theorem norm_pi_le (S : ∀ i, C0Semigroup ℂ (X i)) (t : NNReal)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, ‖S i t‖ ≤ M) :
    ‖pi S t‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg x))).2
  intro i
  calc
    ‖S i t (x i)‖ ≤ ‖S i t‖ * ‖x i‖ := (S i t).le_opNorm (x i)
    _ ≤ M * ‖x‖ := by
      exact mul_le_mul (h i) (norm_le_pi_norm x i) (norm_nonneg _) hM
end Pi
end C0Semigroup
end
