module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v017db2b0e022.Planarwave.Analysis.Semigroup ====
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

/-- The operator at time zero. -/
@[simp]
axiom map_zero (S : C0Semigroup 𝕜 E) : S 0 = ContinuousLinearMap.id 𝕜 E

axiom add_apply (S : C0Semigroup 𝕜 E) (s t : NNReal) (x : E) :
    S (s + t) x = S s (S t x)

/-- Strong continuity of an orbit. -/
protected axiom strongContinuous (S : C0Semigroup 𝕜 E) (x : E) :
    Continuous fun t ↦ S t x

end C0Semigroup

namespace ContractionSemigroup
variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

end ContractionSemigroup

end
end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_6ed00c5ce310f728f446_SemigroupOperations ====
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
/-- Transport a strongly continuous semigroup through a continuous linear equivalence.  This is
the abstract conjugation step used when the paper returns from diffusion eigenvector coordinates
to the original state space. -/
def conjugate (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) : C0Semigroup ℂ F where
  toFun t := (e : E →L[ℂ] F).comp ((S t).comp (e.symm : F →L[ℂ] E))
  map_zero' := by
    ext x
    change e (S 0 (e.symm x)) = x
    simp
  map_add' s t := by
    ext x
    change e (S (s + t) (e.symm x)) =
      e (S s (e.symm (e (S t (e.symm x)))))
    rw [S.add_apply]
    simp
  strongContinuous' x := by
    change Continuous fun t : NNReal ↦ e (S t (e.symm x))
    exact e.continuous.comp (S.strongContinuous (e.symm x))
theorem norm_conjugate_le (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) (t : NNReal) :
    ‖S.conjugate e t‖ ≤ ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
  calc
    ‖S.conjugate e t‖ ≤
        ‖(e : E →L[ℂ] F)‖ * ‖(S t).comp (e.symm : F →L[ℂ] E)‖ :=
      (e : E →L[ℂ] F).opNorm_comp_le _
    _ ≤ ‖(e : E →L[ℂ] F)‖ *
        (‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖) := by
      gcongr
      exact (S t).opNorm_comp_le (e.symm : F →L[ℂ] E)
    _ = ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
      rw [mul_assoc]
end Conjugate
section Pi
variable {ι : Type*} [Fintype ι]
  {X : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
  [∀ i, CompleteSpace (X i)]
end Pi
end C0Semigroup
end
