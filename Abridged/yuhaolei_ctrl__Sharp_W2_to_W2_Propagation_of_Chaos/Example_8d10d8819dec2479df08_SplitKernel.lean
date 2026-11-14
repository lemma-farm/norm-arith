module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.EMetricSpace.PairReduction
public import Mathlib.Data.Set.FiniteExhaustion
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.IsClosedRestrict
public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vfe459ac6488f.SharpWasserstein.Statement ====
public section
/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
/-!
# Definitions of the public statement

The definitions used by the statement in `Challenge.lean`, copied verbatim (this file is generated
by `scripts/sync-statement.py`). The development and `Solution.lean` use these declarations, so
that Comparator finds the same definitions in the Challenge and Solution environments.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpChaos
/-- **Assumption A.** The one-body drift `a` is `L_a`-Lipschitz, the interaction `K` is bounded by
`M`, and `|K(x,y) - K(x',y')| ≤ L₁|x - x'| + L₂|y - y'|`, for constants `L_a, L₁, L₂, M ≥ 0`.
All norms are Euclidean. -/
structure AssumptionA {d : ℕ} (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (La L₁ L₂ M : ℝ) : Prop where
  La_nonneg : 0 ≤ La
  L₁_nonneg : 0 ≤ L₁
  L₂_nonneg : 0 ≤ L₂
  M_nonneg : 0 ≤ M
  lipschitz_a : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖
  norm_K_le : ∀ x y, ‖K x y‖ ≤ M
  lipschitz_K : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖

end SharpChaos

end
end
end

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vfe459ac6488f.SharpWasserstein.Transport ====
public section
@[expose] public section
/-! The actual unnormalized quadratic transport cost on particle configurations.
The surrounding Pi type has its usual sup norm; that norm is deliberately NOT
used as the transport cost. No transport metric theorem is assumed here. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace SharpWasserstein
abbrev Position (d : ℕ) := Fin d → ℝ

end SharpWasserstein

end
end
end

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vfe459ac6488f.SharpWasserstein.Dynamics ====
public section
@[expose] public section
/-! Concrete analytic target of the manuscript. `MainTheorem` below is a
proposition to be proved, NOT a theorem or an axiom. Weak Fokker--Planck
solutions are expressed using genuine derivatives, measures and integrals.
Establishing equivalence with the manuscript's SDEs remains an obligation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Interval
namespace SharpWasserstein

structure BoundedSmoothKernel {d : ℕ}
    (b : Position d → Position d → Position d) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b)
  boundedDerivatives : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry b) z‖ ≤ C

end SharpWasserstein

end
end
end

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vfe459ac6488f.SharpWasserstein.Sharp.SmoothCoefficients ====
public section
/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
/-!
# Smooth coefficients for the smooth case of Theorem 2.1

The development describes positions by their coordinates, `Position d = Fin d → ℝ`, a type whose
norm is the sup norm. The smooth case of Theorem 2.1 is stated for a bounded smooth one-body
drift `a` and a smooth interaction `K` on coordinates, all of whose derivatives are bounded, which
satisfy Assumption A **for the Euclidean norm**. The predicate `IsSmoothCoefficients` records this
through the Euclidean conjugates `euclidMap a` and `euclidMap₂ K`, so that the constants
`L_a, L₁, L₂, M` are exactly those of the paper.

The particle and reference dynamics of the development are driven by the single kernel
`kernelOf a K x y = a x + K x y`, whose particle drift `N⁻¹ ∑ⱼ (a xᵢ + K xᵢ xⱼ)` is the drift
`a xᵢ + N⁻¹ ∑ⱼ K xᵢ xⱼ` of the paper. The development's qualitative hypotheses on that kernel
(`BoundedSmoothKernel` and `KernelBounds` with some sup-norm constants) follow from
`IsSmoothCoefficients`; those constants never enter the final estimate.
-/
@[expose] public section
noncomputable section
open scoped ContDiff
namespace SharpWasserstein.Sharp
variable {d : ℕ}
/-- The Euclidean conjugate `toLp ∘ f ∘ ofLp` of a map on coordinates. -/
def euclidMap (f : Position d → Position d) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x => WithLp.toLp 2 (f (WithLp.ofLp x))
/-- The Euclidean conjugate of an interaction on coordinates. -/
def euclidMap₂ (K : Position d → Position d → Position d) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x y => WithLp.toLp 2 (K (WithLp.ofLp x) (WithLp.ofLp y))

/-- Smooth coefficients for the smooth case of Theorem 2.1: Assumption A for the Euclidean
norm with constants `La, L₁, L₂, M`, smoothness, boundedness of `a`, and bounded derivatives of
every order. -/
structure IsSmoothCoefficients (a : Position d → Position d)
    (K : Position d → Position d → Position d) (La L₁ L₂ M : ℝ) : Prop where
  assumptionA : SharpChaos.AssumptionA (euclidMap a) (euclidMap₂ K) La L₁ L₂ M
  contDiff_a : ContDiff ℝ ∞ a
  contDiff_K : ContDiff ℝ ∞ (Function.uncurry K)
  bounded_a : ∃ C, ∀ x, ‖a x‖ ≤ C
  iteratedFDeriv_a_le : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n a x‖ ≤ C
  iteratedFDeriv_K_le : ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry K) z‖ ≤ C

namespace IsSmoothCoefficients
variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

end IsSmoothCoefficients
end SharpWasserstein.Sharp

end
end
end

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Examples.Example_8d10d8819dec2479df08_SplitKernel ====
/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
/-!
# Split drift/interaction pairs with Euclidean constants

Section 5 of the paper treats the one-body drift `a` and the interaction `K` separately: the
drift of level `m` of the hierarchy is `b^{[m]}_i(x) = a(xᵢ) + N⁻¹ ∑_{j ≤ m} K(xᵢ, xⱼ)` and the
external operator is `Φψ(x, y) = ∑ᵢ K(xᵢ, y) · ∇ᵢψ(x)` (`eq:Bm-Phi`). The constants of
Lemma 5.2 (`lem:pointwise`) are the Euclidean constants `L_a, L₁, L₂, M` of Assumption A.

This file packages the hypotheses used by the sharp hierarchy in the predicate `SplitKernel`:
Assumption A for the Euclidean conjugates, and qualitative smoothness with bounded derivatives
of `a` and `K` separately. It derives the Euclidean first-derivative bounds used in Lemma 5.2,
shows that `IsSmoothCoefficients` implies `SplitKernel`, and that the predicate (with the same
constants) is preserved by the coordinatewise sine periodization used to reduce to periodic
coefficients.

## Main definitions

* `oneBodyKernel a`: the drift `a` as a kernel `(x, y) ↦ a x`.
* `SplitKernel a K La L₁ L₂ M`.

## Main statements

* `SplitKernel.norm_toLp_fderiv_first_le`, `SplitKernel.norm_toLp_fderiv_second_le`,
  `SplitKernel.norm_toLp_K_le`: `‖D_x K‖ ≤ L₁`, `‖D_y K‖ ≤ L₂`, `|K| ≤ M` in Euclidean norms.
* `SplitKernel.of_smooth`: smooth coefficients (`IsSmoothCoefficients`) form a split pair.
* `SplitKernel.sine`, `sine_oneBody_periodic`: the sine-periodized pair.
-/
@[expose] public section
noncomputable section
open scoped ContDiff
namespace SharpWasserstein.Sharp.Hierarchy
variable {d : ℕ}
/-- The one-body drift `a`, regarded as a kernel that ignores its second argument. -/
def oneBodyKernel (a : Position d → Position d) : Position d → Position d → Position d :=
  fun x _ => a x

/-! ### Euclidean first-derivative bounds -/

namespace SplitKernel
variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

end SplitKernel
/-! ### Smooth coefficients are split pairs -/
section SmoothCoefficients
variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}
/-- The one-body drift of smooth coefficients is a bounded smooth kernel. -/
theorem boundedSmooth_oneBody_of_smooth (h : IsSmoothCoefficients a K La L₁ L₂ M) :
    BoundedSmoothKernel (oneBodyKernel a) := by
  have ha : ContDiff ℝ ∞ (fun z : Position d × Position d => a z.1) :=
    h.contDiff_a.comp contDiff_fst
  refine ⟨ha, fun n => ?_⟩
  obtain ⟨Ca, hCa⟩ := h.iteratedFDeriv_a_le n
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨max 0 (Ca * ‖ContinuousLinearMap.fst ℝ (Position d) (Position d)‖ ^ n),
    le_max_left _ _, fun z => ?_⟩
  have hcomp : Function.uncurry (oneBodyKernel a) =
      a ∘ (ContinuousLinearMap.fst ℝ (Position d) (Position d)) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ h.contDiff_a z hn]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (le_max_of_le_right ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hCa _
end SmoothCoefficients
namespace SplitKernel
end SplitKernel
end SharpWasserstein.Sharp.Hierarchy
