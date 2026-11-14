import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Convex.Combination
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.PositiveShift ====
section
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
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/
namespace MarkovProcess.Semigroup
open Filter Set Topology
/-- Positive real parameters, ordered by their underlying real values. -/
abbrev PositiveShift := Set.Ioi (0 : ℝ)

end MarkovProcess.Semigroup

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.ContractiveResolvent ====
section
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
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/
open Filter Topology
namespace MarkovProcess.Semigroup
/-- A resolvent family on a real normed space with the contraction bound and
dense range needed for normalization at large positive shifts. -/
structure ContractiveResolvent (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The resolvent at a positive real shift. -/
  operator : PositiveShift → E →L[ℝ] E
  /-- The resolvent identity, with the sign convention for `(α + A)⁻¹`. -/
  resolvent_identity : ∀ α β,
    operator α - operator β =
      ((β : ℝ) - (α : ℝ)) • ((operator α).comp (operator β))
  /-- The Hille--Yosida contraction estimate. -/
  opNorm_le_inv : ∀ α, ‖operator α‖ ≤ (α : ℝ)⁻¹
  /-- Every resolvent has dense range. -/
  denseRange : ∀ α, DenseRange (operator α)
namespace ContractiveResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The normalized resolvent `α R_α`. -/
def scaledOperator (R : ContractiveResolvent E) (α : PositiveShift) : E →L[ℝ] E :=
  (α : ℝ) • R.operator α

end ContractiveResolvent
end MarkovProcess.Semigroup

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.Basic ====
section
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
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/
open Filter Topology
namespace MarkovProcess.Semigroup
/-- A strongly continuous contraction semigroup on a real normed space. -/
structure StronglyContinuousContractionSemigroup (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The continuous linear time-evolution operator. -/
  operator : NNReal → E →L[ℝ] E
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ E
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ x, Continuous (fun t ↦ operator t x)
namespace StronglyContinuousContractionSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
instance : CoeFun (StronglyContinuousContractionSemigroup E)
    (fun _ ↦ NNReal → E →L[ℝ] E) where
  coe S := S.operator

variable (S : StronglyContinuousContractionSemigroup E)

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E) (t : NNReal),
  ‖S.operator t‖ ≤ 1

end StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.YosidaApproximation ====
section
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
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/
open Filter Topology
open NormedSpace
noncomputable section
namespace MarkovProcess.Semigroup
namespace ContractiveResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/
private instance cacheSMulCLM : SMul ℝ (E →L[ℝ] E) := inferInstance
private instance cacheModuleCLM : Module ℝ (E →L[ℝ] E) := inferInstance
private instance cacheAlgebraCLM : Algebra ℝ (E →L[ℝ] E) := inferInstance
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.cacheIsTopologicalRingCLM.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E],
  IsTopologicalRing (E →L[ℝ] E)
attribute [instance] _root_.MarkovProcess.Semigroup.ContractiveResolvent.cacheIsTopologicalRingCLM
/-- The bounded Yosida generator `G_α = α (α R_α - I)`. -/
def yosidaGenerator (R : ContractiveResolvent E) (α : PositiveShift) : E →L[ℝ] E :=
  (α : ℝ) • (R.scaledOperator α - ContinuousLinearMap.id ℝ E)

section CompleteSpace
variable [CompleteSpace E]
/-- The exponential of the bounded Yosida generator at nonnegative time. -/
def yosidaOperator (R : ContractiveResolvent E) (α : PositiveShift) (t : NNReal) :
    E →L[ℝ] E :=
  exp ((t : ℝ) • R.yosidaGenerator α)

end CompleteSpace

end ContractiveResolvent
end MarkovProcess.Semigroup

end
end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.StrongOperatorLimit ====
section
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
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/
open Filter Topology
namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section Completeness
variable [CompleteSpace E]
/-- The continuous linear map obtained as the pointwise limit of a pointwise
Cauchy sequence of contractions. -/
noncomputable def strongOperatorLimit (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) :
    E →L[ℝ] E :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (fun x ↦ limUnder atTop (fun n ↦ T n x)) T
    (tendsto_pi_nhds.2 fun x ↦ (hcauchy x).tendsto_limUnder)
    (isBounded_iff_forall_norm_le.2
      ⟨1, Set.forall_mem_range.2 fun n ↦ hT n⟩)

end Completeness

end MarkovProcess.Semigroup

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.YosidaStrongLimit ====
section
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
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/
open Filter NormedSpace Set Topology
noncomputable section
namespace MarkovProcess.Semigroup
/-- The canonical sequence of positive shifts, `n + 1`. -/
def naturalShift (n : ℕ) : PositiveShift :=
  ⟨(n : ℝ) + 1, by
    change 0 < (n : ℝ) + 1
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one⟩

namespace ContractiveResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section CompleteSpace
variable [CompleteSpace E]

/-- The canonical Yosida exponential sequence at a fixed time. -/
def yosidaOperatorSequence (R : ContractiveResolvent E) (t : NNReal) :
    ℕ → E →L[ℝ] E :=
  fun n ↦ R.yosidaOperator (naturalShift n) t
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.norm_yosidaOperatorSequence_le_one.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  (R : MarkovProcess.Semigroup.ContractiveResolvent E) (t : NNReal) (n : ℕ),
  ‖R.yosidaOperatorSequence t n‖ ≤ 1
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.cauchySeq_yosidaOperatorSequence_apply.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  (R : MarkovProcess.Semigroup.ContractiveResolvent E) (t : NNReal) (x : E),
  CauchySeq fun (n : ℕ) ↦ (R.yosidaOperatorSequence t n : E → E) x
/-- The canonical strong limit of the Yosida exponential approximants. -/
def yosidaStrongLimit (R : ContractiveResolvent E) (t : NNReal) : E →L[ℝ] E :=
  strongOperatorLimit (R.yosidaOperatorSequence t)
    (R.norm_yosidaOperatorSequence_le_one t)
    (R.cauchySeq_yosidaOperatorSequence_apply t)

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.norm_yosidaStrongLimit_le_one.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : CompleteSpace E] (R : MarkovProcess.Semigroup.ContractiveResolvent E) (t : NNReal),
  ‖R.yosidaStrongLimit t‖ ≤ 1
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.yosidaStrongLimit_zero.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : CompleteSpace E] (R : MarkovProcess.Semigroup.ContractiveResolvent E),
  R.yosidaStrongLimit 0 = ContinuousLinearMap.id ℝ E
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.yosidaStrongLimit_add.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : CompleteSpace E] (R : MarkovProcess.Semigroup.ContractiveResolvent E) (s t : NNReal),
  R.yosidaStrongLimit (s + t) = R.yosidaStrongLimit s ∘SL R.yosidaStrongLimit t
end CompleteSpace
end ContractiveResolvent
end MarkovProcess.Semigroup

end
end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.OrbitContinuity ====
section
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
# Continuity of semigroup orbits from continuity at zero

For a contractive semigroup, strong convergence to the identity at time zero
propagates to continuity of every orbit at every nonnegative time.  Contractivity also upgrades
strong continuity to joint continuity in the time and the vector, in the form
`continuous_operator_apply`.
-/
open Filter Topology
namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.continuous_orbit_of_tendsto_zero.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  (T : NNReal → E →L[ℝ] E),
  (∀ (s t : NNReal), T (s + t) = T s ∘SL T t) →
    (∀ (t : NNReal), ‖T t‖ ≤ 1) →
      (∀ (x : E), Filter.Tendsto (fun (t : NNReal) ↦ (T t : E → E) x) (nhds 0) (nhds x)) →
        ∀ (x : E), Continuous fun (t : NNReal) ↦ (T t : E → E) x
namespace StronglyContinuousContractionSemigroup
def ofTendstoZero
    (T : NNReal → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hcontract : ∀ t, ‖T t‖ ≤ 1)
    (htend : ∀ x, Tendsto (fun t ↦ T t x) (nhds 0) (nhds x)) :
    StronglyContinuousContractionSemigroup E where
  operator := T
  operator_zero := hzero
  operator_add := hadd
  opNorm_le_one := hcontract
  continuous_orbit := continuous_orbit_of_tendsto_zero T hadd hcontract htend
end StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Semigroup.Generation ====
section
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
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/
open Filter NormedSpace Set Topology
noncomputable section
namespace MarkovProcess.Semigroup
namespace ContractiveResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.Semigroup.ContractiveResolvent.tendsto_yosidaStrongLimit_apply_zero.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : CompleteSpace E] (R : MarkovProcess.Semigroup.ContractiveResolvent E) (x : E),
  Filter.Tendsto (fun (t : NNReal) ↦ (R.yosidaStrongLimit t : E → E) x) (nhds 0) (nhds x)
/-- The strongly continuous contraction semigroup generated canonically by a
contractive resolvent through its Yosida approximations. -/
def generatedSemigroup (R : ContractiveResolvent E) :
    StronglyContinuousContractionSemigroup E :=
  StronglyContinuousContractionSemigroup.ofTendstoZero
    R.yosidaStrongLimit R.yosidaStrongLimit_zero R.yosidaStrongLimit_add
    R.norm_yosidaStrongLimit_le_one R.tendsto_yosidaStrongLimit_apply_zero
end ContractiveResolvent
end MarkovProcess.Semigroup

end
end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.Basic ====
section
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
# Sub-Markov kernels

This file records the elementary mass algebra of sub-Markov kernels.  It does
not define transition families or connect kernels to operator semigroups or
stochastic processes.
-/
open MeasureTheory
open scoped ENNReal ProbabilityTheory
namespace MarkovProcess
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
/-- A kernel is sub-Markov if each of its measures has total mass at most one. -/
def IsSubMarkovKernel (κ : ProbabilityTheory.Kernel α β) : Prop :=
  ∀ x, κ x Set.univ ≤ 1
namespace IsSubMarkovKernel
open ProbabilityTheory
variable {κ : Kernel α β} {η : Kernel β γ}

end IsSubMarkovKernel
end MarkovProcess

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.KernelSemigroup ====
section
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
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/
open Set
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace MarkovProcess
open MeasureTheory ProbabilityTheory
/-- A jointly measurable sub-Markov transition-kernel semigroup.

The measurability field is joint in time and starting point.  The composition
orientation agrees with the convention that the operator associated with a
kernel `K` sends `f` to `x ↦ ∫ y, f y ∂K x`.
-/
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  /-- The transition kernel at a nonnegative time. -/
  kernel : NNReal → Kernel α α
  /-- Joint measurability in time and starting point. -/
  measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
  /-- At time zero the transition kernel is the identity kernel. -/
  kernel_zero : kernel 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)
namespace SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
instance : CoeFun (SubMarkovKernelSemigroup α)
    (fun _ ↦ NNReal → Kernel α α) where
  coe P := P.kernel

variable (P : SubMarkovKernelSemigroup α)

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.SubMarkovKernelSemigroup.measure_univ_le_one.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] (P : MarkovProcess.SubMarkovKernelSemigroup α)
  (t : NNReal) (x : α),
  ((P.kernel t : α → MeasureTheory.Measure α) x : Set α → ENNReal) Set.univ ≤ 1

namespace IsConservative
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

end
end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.MeasurableRadonFamily ====
section
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
# Measurability of finite Radon measure families

On a second-countable locally compact Hausdorff space, a family of finite
regular measures is measurable when integration against every compactly
supported real continuous function is measurable.  The proof uses compact
exhaustions and Urysohn cutoffs to make every open-set evaluation a countable
supremum of measurable test integrals, then applies Mathlib's Giry
π-system criterion.

The compact exhaustion and cutoff choices are private implementation details.
-/
open scoped CompactlySupported ENNReal NNReal Topology
open Set MeasureTheory TopologicalSpace
namespace MeasureTheory
namespace MeasurableRadonFamily
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

end MeasurableRadonFamily
set_option linter.unusedVariables false in
axiom _root_.MeasureTheory.measurable_measure_of_measurable_integral_compactlySupported.{w_u_1,w_u_2} : ∀ {Q : Type w_u_1} {X : Type w_u_2} [inst : MeasurableSpace Q] [inst_1 : TopologicalSpace X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [inst_5 : MeasurableSpace X]
  [BorelSpace X] (μ : Q → MeasureTheory.Measure X) [∀ (q : Q), (μ q).Regular]
  [∀ (q : Q), MeasureTheory.IsFiniteMeasure (μ q)],
  (∀ (f : CompactlySupportedContinuousMap X ℝ),
      Measurable fun (q : Q) ↦ ∫ (x : X), (f : X → ℝ) x ∂μ q) →
    Measurable μ
end MeasureTheory

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0OperatorMeasure ====
section
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
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/
open CompactlySupported MeasureTheory
open scoped ZeroAtInfty
namespace MarkovProcess
variable {α : Type*} [TopologicalSpace α]
namespace PositiveC0OperatorMeasure
/-- Pointwise preservation of nonnegative functions by an operator on `C₀(α, ℝ)`. -/
def IsPositive (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) : Prop :=
  ∀ f : C₀(α, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x
noncomputable def compactlySupportedToC0LinearMap : C_c(α, ℝ) →ₗ[ℝ] C₀(α, ℝ) where
  toFun f := f
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)
/-- Evaluation at `x` after applying `T`, restricted from `C₀(α, ℝ)` to compactly supported
continuous functions, as a positive linear functional. -/
noncomputable def functional (x : α) : C_c(α, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f ↦ T (compactlySupportedToC0LinearMap f) x
      map_add' := by
        intro f g
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro c f
        rw [map_smul, map_smul]
        rfl }
    fun f hf ↦ hT (compactlySupportedToC0LinearMap f) (fun y ↦ hf y) x
variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]
/-- The regular Riesz measure representing point evaluation after applying `T`. -/
noncomputable def measure (x : α) : Measure α :=
  RealRMK.rieszMeasure (functional T hT x)
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0OperatorMeasure.regular_measure.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α]
  (T : ZeroAtInftyContinuousMap α ℝ →L[ℝ] ZeroAtInftyContinuousMap α ℝ)
  (hT : MarkovProcess.PositiveC0OperatorMeasure.IsPositive T) [inst_1 : T2Space α]
  [inst_2 : LocallyCompactSpace α] [inst_3 : MeasurableSpace α] [inst_4 : BorelSpace α] (x : α),
  (MarkovProcess.PositiveC0OperatorMeasure.measure T hT x).Regular
attribute [instance] _root_.MarkovProcess.PositiveC0OperatorMeasure.regular_measure

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0OperatorMeasure.integral_measure.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α]
  (T : ZeroAtInftyContinuousMap α ℝ →L[ℝ] ZeroAtInftyContinuousMap α ℝ)
  (hT : MarkovProcess.PositiveC0OperatorMeasure.IsPositive T) [inst_1 : T2Space α]
  [inst_2 : LocallyCompactSpace α] [inst_3 : MeasurableSpace α] [inst_4 : BorelSpace α] (x : α)
  (f : CompactlySupportedContinuousMap α ℝ),
  ∫ (y : α), (f : α → ℝ) y ∂MarkovProcess.PositiveC0OperatorMeasure.measure T hT x =
    ((T : ZeroAtInftyContinuousMap α ℝ → ZeroAtInftyContinuousMap α ℝ)
          ((MarkovProcess.PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap :
              CompactlySupportedContinuousMap α ℝ → ZeroAtInftyContinuousMap α ℝ)
            f) :
        α → ℝ)
      x
end PositiveC0OperatorMeasure
end MarkovProcess

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0OperatorMass ====
section
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
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/
open CompactlySupported MeasureTheory
open scoped ZeroAtInfty
namespace MarkovProcess.PositiveC0OperatorMeasure
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0OperatorMeasure.isFiniteMeasure_measure.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] [inst_2 : LocallyCompactSpace α]
  [inst_3 : MeasurableSpace α] [inst_4 : BorelSpace α]
  (T : ZeroAtInftyContinuousMap α ℝ →L[ℝ] ZeroAtInftyContinuousMap α ℝ)
  (hT : MarkovProcess.PositiveC0OperatorMeasure.IsPositive T),
  ‖T‖ ≤ 1 →
    ∀ (x : α),
      MeasureTheory.IsFiniteMeasure (MarkovProcess.PositiveC0OperatorMeasure.measure T hT x)
end MarkovProcess.PositiveC0OperatorMeasure

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0OperatorKernel ====
section
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
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/
open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty
namespace MarkovProcess.PositiveC0OperatorKernel
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)

/-- The kernel whose value at `x` is the Riesz measure representing evaluation of `T` at `x`. -/
noncomputable def kernel (hT_norm : ‖T‖ ≤ 1) : Kernel α α := by
  letI : ∀ x, IsFiniteMeasure (PositiveC0OperatorMeasure.measure T hT x) :=
    fun x ↦ PositiveC0OperatorMeasure.isFiniteMeasure_measure T hT hT_norm x
  exact
    { toFun := PositiveC0OperatorMeasure.measure T hT
      measurable' :=
        measurable_measure_of_measurable_integral_compactlySupported
          (PositiveC0OperatorMeasure.measure T hT) fun f ↦ by
            rw [show (fun x ↦ ∫ y, f y ∂PositiveC0OperatorMeasure.measure T hT x) =
              fun x ↦ T (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) x by
                funext x
                exact PositiveC0OperatorMeasure.integral_measure T hT x f]
            exact
              (T (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f)).continuous
                |>.measurable }

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0OperatorKernel.isSubMarkovKernel_kernel.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] [inst_2 : LocallyCompactSpace α]
  [inst_3 : SecondCountableTopology α] [inst_4 : MeasurableSpace α] [inst_5 : BorelSpace α]
  (T : ZeroAtInftyContinuousMap α ℝ →L[ℝ] ZeroAtInftyContinuousMap α ℝ)
  (hT : MarkovProcess.PositiveC0OperatorMeasure.IsPositive T) (hT_norm : ‖T‖ ≤ 1),
  MarkovProcess.IsSubMarkovKernel (MarkovProcess.PositiveC0OperatorKernel.kernel T hT hT_norm)

end MarkovProcess.PositiveC0OperatorKernel

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0SemigroupKernel ====
section
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
# Kernel semigroups represented by positive contraction semigroups on `C₀`

A strongly continuous semigroup of positive contractions on real continuous functions vanishing
at infinity determines a jointly measurable sub-Markov kernel semigroup.
-/
open CompactlySupported MeasureTheory ProbabilityTheory
open scoped ENNReal ZeroAtInfty
namespace MarkovProcess.PositiveC0SemigroupKernel
open MarkovProcess.Semigroup
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0SemigroupKernel.measurable_kernel.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] [inst_2 : LocallyCompactSpace α]
  [inst_3 : SecondCountableTopology α] [inst_4 : MeasurableSpace α] [inst_5 : BorelSpace α]
  (S :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (ZeroAtInftyContinuousMap α ℝ))
  (hS : ∀ (t : NNReal), MarkovProcess.PositiveC0OperatorMeasure.IsPositive (S.operator t)),
  Measurable fun (p : NNReal × α) ↦
    (MarkovProcess.PositiveC0OperatorKernel.kernel (S.operator p.1) (hS p.1)
          (MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one S
            p.1) :
        α → MeasureTheory.Measure α)
      p.2
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0SemigroupKernel.kernel_zero.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] [inst_2 : LocallyCompactSpace α]
  [inst_3 : SecondCountableTopology α] [inst_4 : MeasurableSpace α] [inst_5 : BorelSpace α]
  (S :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (ZeroAtInftyContinuousMap α ℝ))
  (hS : ∀ (t : NNReal), MarkovProcess.PositiveC0OperatorMeasure.IsPositive (S.operator t)),
  MarkovProcess.PositiveC0OperatorKernel.kernel (S.operator 0) (hS 0)
      (MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one S 0) =
    ProbabilityTheory.Kernel.id
set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0SemigroupKernel.kernel_add.{w_u_1} : ∀ {α : Type w_u_1} [inst : TopologicalSpace α] [inst_1 : T2Space α] [inst_2 : LocallyCompactSpace α]
  [inst_3 : SecondCountableTopology α] [inst_4 : MeasurableSpace α] [inst_5 : BorelSpace α]
  (S :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (ZeroAtInftyContinuousMap α ℝ))
  (hS : ∀ (t : NNReal), MarkovProcess.PositiveC0OperatorMeasure.IsPositive (S.operator t))
  (s t : NNReal),
  MarkovProcess.PositiveC0OperatorKernel.kernel (S.operator (s + t)) (hS (s + t))
      (MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one S
        (s + t)) =
    (MarkovProcess.PositiveC0OperatorKernel.kernel (S.operator t) (hS t)
          (MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one S
            t)).comp
      (MarkovProcess.PositiveC0OperatorKernel.kernel (S.operator s) (hS s)
        (MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.norm_operator_le_one S s))
/-- The sub-Markov kernel semigroup represented by a positive contraction semigroup on `C₀`. -/
noncomputable def kernelSemigroup : SubMarkovKernelSemigroup α where
  kernel t := PositiveC0OperatorKernel.kernel (S t) (hS t) (S.norm_operator_le_one t)
  measurable_kernel := measurable_kernel S hS
  kernel_zero := kernel_zero S hS
  kernel_add := kernel_add S hS
  isSubMarkovKernel t :=
    PositiveC0OperatorKernel.isSubMarkovKernel_kernel
      (S t) (hS t) (S.norm_operator_le_one t)

end MarkovProcess.PositiveC0SemigroupKernel

end

-- ==== Examples.scottnarmstrong__MarkovProcess.Dependencies.v98af1febc7a9.MarkovProcess.Kernel.PositiveC0Resolvent ====
section
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
# Positive `C₀` resolvents and their Feller kernels

A positive contractive resolvent on `C₀` canonically generates a strongly continuous semigroup
of positive contractions.  The existing pointwise Riesz construction then represents that
semigroup by a sub-Markov kernel semigroup and identifies its `C₀` operators exactly.

The package in this file starts from the resolvent identity, the Hille--Yosida bound, dense range,
and positivity of the actual shifted resolvents.  It assumes neither a semigroup nor a kernel.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty
noncomputable section
namespace MarkovProcess
open MarkovProcess.Semigroup
variable (X : Type*) [TopologicalSpace X]
/-- A contractive resolvent on `C₀(X, ℝ)` whose shifted operators preserve nonnegative
functions. -/
structure PositiveC0ContractiveResolvent extends ContractiveResolvent C₀(X, ℝ) where
  /-- Every shifted resolvent is positivity preserving. -/
  isPositive : ∀ alpha,
    PositiveC0OperatorMeasure.IsPositive (toContractiveResolvent.operator alpha)
namespace PositiveC0ContractiveResolvent
variable {X : Type*} [TopologicalSpace X]

variable (R : PositiveC0ContractiveResolvent X)

set_option linter.unusedVariables false in
axiom _root_.MarkovProcess.PositiveC0ContractiveResolvent.isPositive_generatedSemigroup.{w_u_2} : ∀ {X : Type w_u_2} [inst : TopologicalSpace X] (R : MarkovProcess.PositiveC0ContractiveResolvent X)
  (t : NNReal), MarkovProcess.PositiveC0OperatorMeasure.IsPositive (R.generatedSemigroup.operator t)
section Kernel
variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
/-- The sub-Markov kernel semigroup represented by the canonical positive `C₀` semigroup. -/
noncomputable def kernelSemigroup : SubMarkovKernelSemigroup X :=
  PositiveC0SemigroupKernel.kernelSemigroup
    R.toContractiveResolvent.generatedSemigroup R.isPositive_generatedSemigroup

end Kernel
end PositiveC0ContractiveResolvent
end MarkovProcess

end
end

-- ==== Examples.scottnarmstrong__MarkovProcess.Examples.Example_71b2a108c634e5574a7f_OnePointExtension ====
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
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/
open Filter Set Topology TopologicalSpace
noncomputable section
namespace OnePoint
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

end OnePoint
namespace MarkovProcess.PositiveC0ContractiveResolvent
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]
/-- The part of a function on the one-point compactification which vanishes at infinity. -/
noncomputable def onePointRemainder (g : C₀(OnePoint X, ℝ)) : C₀(X, ℝ) where
  toFun x := g (x : OnePoint X) - g OnePoint.infty
  continuous_toFun :=
    (g.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hg := (OnePoint.continuous_iff (g : OnePoint X → ℝ)).mp g.continuous
    rw [← Filter.coclosedCompact_eq_cocompact]
    simpa only [Function.comp_apply, sub_self] using hg.1.sub_const (g OnePoint.infty)
/-- Reassemble a vanishing function and its value at infinity. -/
noncomputable def onePointAssemble (f : C₀(X, ℝ)) (c : ℝ) : C₀(OnePoint X, ℝ) :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
    (OnePoint.continuousMapMk (f.toContinuousMap + ContinuousMap.const X c) c (by
      rw [Filter.coclosedCompact_eq_cocompact]
      simpa only [ContinuousMap.coe_add, ContinuousMap.coe_const, Pi.add_apply, zero_add]
        using! (zero_at_infty f).add_const c))

variable [MeasurableSpace X] [BorelSpace X]
variable (R : PositiveC0ContractiveResolvent X)
/-- Extend the generated semigroup action by fixing the value at infinity. -/
noncomputable def onePointSemigroupAction (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    C₀(OnePoint X, ℝ) :=
  onePointAssemble
    (R.toContractiveResolvent.generatedSemigroup t (onePointRemainder g))
    (g OnePoint.infty)


set_option linter.unusedVariables false in
private theorem norm_onePointSemigroupAction_le (t : NNReal) (g : C₀(OnePoint X, ℝ)) 
    (h_MarkovProcess_PositiveC0ContractiveResolvent_onePointSemigroupAction_infty : ∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : T2Space X]
      (R : MarkovProcess.PositiveC0ContractiveResolvent X) (t : NNReal)
      (g : ZeroAtInftyContinuousMap (OnePoint X) ℝ),
      (R.onePointSemigroupAction t g : OnePoint X → ℝ) OnePoint.infty =
        (g : OnePoint X → ℝ) OnePoint.infty)
    (h_MarkovProcess_PositiveC0ContractiveResolvent_onePointSemigroupAction_coe : ∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : T2Space X] [inst_2 : LocallyCompactSpace X]
      [inst_3 : SecondCountableTopology X] [inst_4 : MeasurableSpace X] [inst_5 : BorelSpace X]
      (R : MarkovProcess.PositiveC0ContractiveResolvent X) (t : NNReal)
      (g : ZeroAtInftyContinuousMap (OnePoint X) ℝ) (x : X),
      (R.onePointSemigroupAction t g : OnePoint X → ℝ) (↑x : OnePoint X) =
        ∫ (y : X),
            (g : OnePoint X → ℝ)
              (↑y : OnePoint X) ∂(R.kernelSemigroup.kernel t : X → MeasureTheory.Measure X) x +
          (1 - ((R.kernelSemigroup.kernel t : X → MeasureTheory.Measure X) x).real Set.univ) *
            (g : OnePoint X → ℝ) OnePoint.infty)
    :
    ‖R.onePointSemigroupAction t g‖ ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun z ↦ ?_
  induction z using OnePoint.rec with
  | infty =>
      change ‖R.onePointSemigroupAction t g OnePoint.infty‖ ≤ ‖g‖
      rw [h_MarkovProcess_PositiveC0ContractiveResolvent_onePointSemigroupAction_infty]
      exact g.toBCF.norm_coe_le_norm OnePoint.infty
  | coe x =>
      change ‖R.onePointSemigroupAction t g (x : OnePoint X)‖ ≤ ‖g‖
      rw [Real.norm_eq_abs, h_MarkovProcess_PositiveC0ContractiveResolvent_onePointSemigroupAction_coe]
      let μ := R.kernelSemigroup t x
      have hmassE : μ Set.univ ≤ 1 := R.kernelSemigroup.measure_univ_le_one t x
      have hfin : μ Set.univ < ⊤ := lt_of_le_of_lt hmassE ENNReal.one_lt_top
      let : IsFiniteMeasure μ := ⟨hfin⟩
      have hmass0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
      have hmass1 : μ.real Set.univ ≤ 1 := by
        rw [measureReal_def]
        simpa only [ENNReal.toReal_one] using
          (ENNReal.toReal_le_toReal hfin.ne ENNReal.one_ne_top).mpr hmassE
      have hint : |∫ y, g (y : OnePoint X) ∂μ| ≤ ‖g‖ * μ.real Set.univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const
          (ae_of_all μ fun y ↦ g.toBCF.norm_coe_le_norm (y : OnePoint X))
      calc
        |∫ y, g (y : OnePoint X) ∂μ +
            (1 - μ.real Set.univ) * g OnePoint.infty| ≤
            |∫ y, g (y : OnePoint X) ∂μ| +
              |(1 - μ.real Set.univ) * g OnePoint.infty| := abs_add_le _ _
        _ ≤ ‖g‖ * μ.real Set.univ +
              (1 - μ.real Set.univ) * ‖g‖ := by
          refine add_le_add hint ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hmass1)]
          exact mul_le_mul_of_nonneg_left
            (g.toBCF.norm_coe_le_norm OnePoint.infty) (sub_nonneg.mpr hmass1)
        _ = ‖g‖ := by ring
end MarkovProcess.PositiveC0ContractiveResolvent
