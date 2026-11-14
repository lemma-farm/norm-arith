module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.BUC ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
@[expose] public section
/-!
# Bounded uniformly continuous functions

This file bundles bounded uniformly continuous functions.  The norm and metric are inherited from
`BoundedContinuousFunction`, so the norm is the supremum norm.  In particular, this is a Banach
space whenever the codomain is a Banach space.

The basic pre- and postcomposition operations below are intended to support convolution operators
and, in particular, the heat semigroup on Euclidean space.
-/
open Bornology Filter Function Set Topology
open scoped BoundedContinuousFunction Topology
universe u v w
noncomputable section
/-- A bounded uniformly continuous function from `α` to `E`.

The bounded continuous function is stored explicitly so that the supremum norm and the existing
`BoundedContinuousFunction` API can be reused. -/
structure BUC (α : Type u) (E : Type v) [UniformSpace α] [PseudoMetricSpace E] where
  /-- The underlying bounded continuous function. -/
  toBCF : α →ᵇ E
  /-- The underlying function is uniformly continuous. -/
  uniformContinuous' : UniformContinuous (toBCF : α → E)
namespace BUC
variable {α : Type u} {β : Type v} {E : Type w}
section Basic
variable [UniformSpace α] [PseudoMetricSpace E]
instance instFunLike : FunLike (BUC α E) α E where
  coe f := f.toBCF
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact BoundedContinuousFunction.ext fun x ↦ congr_fun h x
/-- Reinterpret a bounded uniformly continuous function as a bounded continuous function. -/
instance instCoeBCF : Coe (BUC α E) (α →ᵇ E) := ⟨toBCF⟩

axiom toBCF_injective : Injective (toBCF : BUC α E → α →ᵇ E)
/-- A bounded uniformly continuous function is uniformly continuous. -/
protected axiom uniformContinuous (f : BUC α E) : UniformContinuous (f : α → E)

end Basic
section Algebra
variable [UniformSpace α] [NormedAddCommGroup E]
instance instZero : Zero (BUC α E) := ⟨⟨0, uniformContinuous_const⟩⟩
@[simp]
axiom coe_zero : ⇑(0 : BUC α E) = 0

instance instAdd : Add (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF + g.toBCF, f.uniformContinuous.add g.uniformContinuous⟩⟩
@[simp]
axiom coe_add (f g : BUC α E) : ⇑(f + g) = f + g

instance instSMulNat : SMul ℕ (BUC α E) where
  smul n f := nsmulRec n f
set_option linter.unusedVariables false in
axiom _root_.BUC.coe_nsmul.{w_u,w_w} : ∀ {α : Type w_u} {E : Type w_w} [inst : UniformSpace α] [inst_1 : NormedAddCommGroup E]
  (f : BUC α E) (n : ℕ), (⇑(n • f) : α → E) = n • (⇑f : α → E)
instance instNeg : Neg (BUC α E) := ⟨fun f ↦ ⟨-f.toBCF, f.uniformContinuous.neg⟩⟩
@[simp]
axiom coe_neg (f : BUC α E) : ⇑(-f) = -f

instance instSub : Sub (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF - g.toBCF, f.uniformContinuous.sub g.uniformContinuous⟩⟩
@[simp]
axiom coe_sub (f g : BUC α E) : ⇑(f - g) = f - g

instance instSMulInt : SMul ℤ (BUC α E) where
  smul z f := zsmulRec (· • ·) z f
@[simp]
axiom coe_zsmul (z : ℤ) (f : BUC α E) : ⇑(z • f) = z • ⇑f
instance instAddCommGroup : AddCommGroup (BUC α E) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun f n ↦ coe_nsmul f n) fun _ _ ↦ coe_zsmul _ _
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
instance instSMul : SMul 𝕜 (BUC α E) :=
  ⟨fun c f ↦ ⟨c • f.toBCF, f.uniformContinuous.const_smul c⟩⟩
@[simp]
axiom coe_smul (c : 𝕜) (f : BUC α E) : ⇑(c • f) = c • ⇑f

instance instModule : Module 𝕜 (BUC α E) := fast_instance%
  Function.Injective.module 𝕜
    ⟨⟨(⇑), coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul
end Algebra
section PseudoMetric
variable [UniformSpace α] [PseudoMetricSpace E]
/-- The uniform metric inherited from bounded continuous functions. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (BUC α E) :=
  PseudoMetricSpace.induced toBCF inferInstance

end PseudoMetric
section Metric
variable [UniformSpace α] [MetricSpace E]
/-- The uniform metric is a genuine metric when the codomain metric is. -/
noncomputable instance instMetricSpace : MetricSpace (BUC α E) :=
  MetricSpace.induced toBCF toBCF_injective inferInstance

end Metric
section Norm
variable [UniformSpace α] [NormedAddCommGroup E]
/-- The supremum norm inherited from bounded continuous functions. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (BUC α E) := fast_instance%
  NormedAddCommGroup.induced _ _
    (⟨⟨toBCF, rfl⟩, fun _ _ ↦ rfl⟩ : BUC α E →+ α →ᵇ E) toBCF_injective

/-- Point evaluation is bounded by the supremum norm. -/
axiom norm_apply_le (f : BUC α E) (x : α) : ‖f x‖ ≤ ‖f‖

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
instance instNormedSpace : NormedSpace 𝕜 (BUC α E) where
  norm_smul_le c f := by
    change ‖c • f.toBCF‖ ≤ ‖c‖ * ‖f.toBCF‖
    exact norm_smul_le c f.toBCF

end Norm
section Postcomp
variable [UniformSpace α]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

end Postcomp
section Translate
variable [NormedAddCommGroup α] [NormedAddCommGroup E]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

end Translate
end BUC

end
end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.BUCCompactSupport ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
namespace BUC
noncomputable section
variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]
/-- Compactly supported continuous tests belong to the BUC space. -/
def ofCompactSupport (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f) : BUC X F :=
  { toBCF :=
      { toFun := f
        continuous_toFun := hf
        map_bounded' := by
          obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
          exact ⟨2 * C, fun x y ↦ (dist_le_norm_add_norm _ _).trans
            (by linarith [hC ⟨x, rfl⟩, hC ⟨y, rfl⟩])⟩ }
    uniformContinuous' := hc.uniformContinuous_of_continuous hf }
variable [MeasurableSpace X] [BorelSpace X] [NormedSpace ℝ F]
end
end BUC

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.TemporalCutoff ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The temporal cutoff in the tracking scheme

Construct the smooth nonnegative unit-mass cutoff supported on `[1/4,3/4]`
specified in Section 1.3 and used in the delayed forcing in Section 4.2.
-/
open MeasureTheory Set
open scoped ContDiff
namespace Planarwave
noncomputable section
def trackingBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num
/-- The paper's temporal cutoff `ρ`, normalized with respect to Lebesgue measure. -/
def trackingCutoff : BUC ℝ ℝ :=
  BUC.ofCompactSupport (trackingBump.normed volume)
    trackingBump.continuous_normed trackingBump.hasCompactSupport_normed

/-- A partially accumulated pulse has mass between zero and one. -/
axiom integral_trackingCutoff_shift_mem {b t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, trackingCutoff (r - b)) ∈ Icc (0 : ℝ) 1
end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.HeatFlow ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The Gaussian heat flow on a finite-dimensional Euclidean space

This file starts the analytic infrastructure used in the proof of the effective-front theorem.
We realize the heat flow probabilistically: at time `t`, with diffusivity `a`, one averages a
function over a centred Gaussian displacement of standard deviation `sqrt (2 * a * t)`.

The definition is made for functions with values in an arbitrary real Banach space.  The lemmas
below establish the zero-time identity, linearity, preservation of constants, and the sharp
supremum-norm contraction.  Later files add the semigroup, smoothing, and heat-equation
properties needed for the Cole--Hopf argument.
-/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Planarwave
section HeatFlow
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- The spatial standard deviation in the heat flow with diffusivity `a` at time `t`. -/
noncomputable def heatScale (a t : ℝ) : ℝ := Real.sqrt (2 * a * t)

/-- Gaussian realization of the heat flow `exp (t * a * Δ)`.

For the PDE applications we use this only when `0 ≤ a` and `0 ≤ t`.  Keeping the definition
total is convenient in Lean; the mathematical properties state the required sign hypotheses.
-/
noncomputable def heatFlow (a t : ℝ) (f : E → F) (x : E) : F :=
  ∫ z, f (x + heatScale a t • z) ∂(stdGaussian E)

/-- The Gaussian heat flow is a contraction in the supremum norm. -/
axiom norm_heatFlow_le {a t C : ℝ} {f : E → F} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ‖heatFlow a t f x‖ ≤ C
/-- Gaussian averaging preserves uniform continuity. -/
axiom uniformContinuous_heatFlow {a t C : ℝ} {f : E → F}
    (hf : UniformContinuous f) (hC : ∀ x, ‖f x‖ ≤ C) :
    UniformContinuous (heatFlow a t f)
axiom continuous_heatFlow {a t C : ℝ} {f : E → F}
    (hf : UniformContinuous f) (hC : ∀ x, ‖f x‖ ≤ C) :
    Continuous (heatFlow a t f)

end HeatFlow
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.HeatSemigroup ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The heat semigroup on bounded uniformly continuous functions

This file bundles the Gaussian heat flow as a contraction on `BUC`.  It is the functional-analytic
form of the heat evolution used in Sections 3, 5, and 6 of the cited paper.
-/
open Filter MeasureTheory ProbabilityTheory
namespace Planarwave
noncomputable section
section HeatSemigroup
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- Gaussian heat evolution, bundled as a bounded uniformly continuous function. -/
def heatFlowBUC (a t : ℝ) (f : BUC E F) : BUC E F where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup
    (heatFlow a t f)
    (continuous_heatFlow f.uniformContinuous (fun x ↦ f.norm_apply_le x))
    ‖f‖
    (fun x ↦ norm_heatFlow_le (fun y ↦ f.norm_apply_le y) x)
  uniformContinuous' :=
    uniformContinuous_heatFlow f.uniformContinuous (fun x ↦ f.norm_apply_le x)

/-- The heat flow is a contraction in the BUC supremum norm. -/
axiom norm_heatFlowBUC_le (a t : ℝ) (f : BUC E F) : ‖heatFlowBUC a t f‖ ≤ ‖f‖

end HeatSemigroup
end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.DelayedHeatForcing ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The delayed forcing of Section 4.2

The natural index `k` below represents the paper's positive integer `k+1`.
Only the preceding unit time interval enters each forcing pulse. The source
will be the adjoint projection of the front's nonlinear remainder.
-/
open MeasureTheory Set
namespace Planarwave
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- The source accumulated during a single completed time block. -/
def delayedHeatBlock (a : ℝ) (N : ℝ → BUC E F) (k : ℕ) : BUC E F :=
  ∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a ((k : ℝ) + 1 - r) (N r)
/-- Equation `eq:defgnew`, including the initial-data pulse. -/
def delayedHeatForcing (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  trackingCutoff t • heatFlowBUC a t p +
    ∑' k : ℕ, trackingCutoff (t - ((k : ℝ) + 1)) •
      heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k)

end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v97bad57befe9.Planarwave.Analysis.HeatDuhamel ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Continuous heat Duhamel trajectories

These facts support both the tracking cancellation and the construction of
the forced Cole--Hopf mild solution. All integrals are BUC-valued; continuity
of the heat operators in operator norm at time zero is not assumed.
-/
open MeasureTheory Set
namespace Planarwave
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- The transverse heat Duhamel integral in real BUC space. -/
def heatDuhamel (a : ℝ) (g : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  ∫ r in (0 : ℝ)..t, heatFlowBUC a (t - r) (g r)
end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_73c874eec01cac6dadec_DelayedHeatForcingCancellation ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Cancellation of completed forcing pulses

The semigroup law and the cutoff's unit integral are the mechanism behind
Step 3b of the nonlinear iteration. The initial pulse exactly cancels the
critical initial heat orbit. Each completed delayed pulse exactly cancels
the critical Duhamel contribution of its preceding source block.
-/
open MeasureTheory Set
namespace Planarwave
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The fully cancelled critical expression depends on at most the last
two time blocks. This is the formula used to estimate `ζ` in Step 3b. -/
axiom heatCriticalResidual_eq_recent {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (0 : ℝ) ((n : ℝ) + 1 + τ))) :
    heatFlowBUC a ((n : ℝ) + 1 + τ) p + heatDuhamel a N ((n : ℝ) + 1 + τ) -
      heatDuhamel a (delayedHeatForcing a p N) ((n : ℝ) + 1 + τ) =
      (∫ r in (n : ℝ)..(n : ℝ) + 1 + τ, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) -
      (∫ r in (0 : ℝ)..(n : ℝ) + 1 + τ, trackingCutoff (r - ((n : ℝ) + 1))) •
        (∫ r in (n : ℝ)..(n : ℝ) + 1, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r))
/-- The cancellation bounds the critical residual solely by the source on
its last two blocks, independently of all earlier history and initial data. -/
theorem norm_heatCriticalResidual_le {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (0 : ℝ) ((n : ℝ) + 1 + τ)))
    (hM : 0 ≤ M) (hbound : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1 + τ), ‖N r‖ ≤ M) :
    ‖heatFlowBUC a ((n : ℝ) + 1 + τ) p + heatDuhamel a N ((n : ℝ) + 1 + τ) -
      heatDuhamel a (delayedHeatForcing a p N) ((n : ℝ) + 1 + τ)‖ ≤ 3 * M := by
  have ht : 0 ≤ (n : ℝ) + 1 + τ := by have := Nat.cast_nonneg (α := ℝ) n; linarith [hτ.1]
  have hmass := integral_trackingCutoff_shift_mem (b := (n : ℝ) + 1) ht
  have hb (b : ℝ) (hnb : (n : ℝ) ≤ b) (hbt : b ≤ (n : ℝ) + 1 + τ) :
      ‖∫ r in (n : ℝ)..b, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M * (b - n) := by
    have hnorm : ∀ r ∈ uIoc (n : ℝ) b,
        ‖heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M := by
      intro r hr
      rw [uIoc_of_le hnb] at hr
      exact (norm_heatFlowBUC_le _ _ _).trans (hbound r ⟨hr.1.le, hr.2.trans hbt⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hnb)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  have hfirst := hb ((n : ℝ) + 1 + τ) (by linarith [hτ.1]) le_rfl
  have hsecond : ‖∫ r in (n : ℝ)..(n : ℝ) + 1,
      heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M := by
    simpa only [add_sub_cancel_left, mul_one] using hb ((n : ℝ) + 1) (by linarith) (by linarith [hτ.1])
  rw [heatCriticalResidual_eq_recent ha p N n hτ hN]
  calc
    _ ≤ ‖∫ r in (n : ℝ)..(n : ℝ) + 1 + τ, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ +
        ‖(∫ r in (0 : ℝ)..(n : ℝ) + 1 + τ, trackingCutoff (r - ((n : ℝ) + 1))) •
          (∫ r in (n : ℝ)..(n : ℝ) + 1, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r))‖ := norm_sub_le _ _
    _ ≤ M * (((n : ℝ) + 1 + τ) - n) + M := by
      apply add_le_add hfirst
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmass.1]
      exact (mul_le_mul hmass.2 hsecond (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
    _ ≤ 3 * M := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hτ.2)]
end
end Planarwave
