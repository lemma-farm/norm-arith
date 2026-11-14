module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Aesop.Constants
public import Aesop.Exception
public import Aesop.Forward.State.ApplyGoalDiff
public import Aesop.Forward.State.Initial
public import Aesop.Script.OptimizeSyntax
public import Aesop.Script.StructureDynamic
public import Aesop.Script.StructureStatic
public import Aesop.Script.UScriptToSScript
public import Aesop.Script.Util
public import Aesop.Search.Expansion.Basic
public import Aesop.Search.Expansion.Simp
public import Aesop.Search.Queue
public import Aesop.Tree.Free
public import Aesop.Tree.Stats
public import Aesop.Util.EqualUpToIds
public import Aesop.Util.Tactic
public import Aesop.Util.Tactic.Unfold
public import Aesop.Util.UnionFind
public import Batteries.Data.UInt
public import Batteries.Lean.HashSet
public import Batteries.Lean.Meta.DiscrTree
public import Batteries.Lean.Meta.Inaccessible
public import Batteries.Lean.PersistentHashSet
public import ImportGraph.Imports.ImportGraph
public import ImportGraph.Lean.Environment
public import Init.Control.Option
public import Init.Control.Reader
public import Init.Control.State
public import Init.Control.StateRef
public import Lean.Compiler.IR.CompilerM
public import Lean.Meta.CollectMVars
public import Lean.Meta.DiscrTree.Main
public import Lean.Meta.SynthInstance
public import Lean.Meta.Tactic.Simp.Rewrite
public import Lean.Meta.Tactic.Split
public import Lean.Meta.WHNF
public import Lean.Parser.Term.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.List.Enum
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.DSimpPercent
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Probability.Notation
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Lean.Meta.Tactic.Simp.Attr
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Fintype.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

-- ==== Examples.roos_j__lean_dfr.Examples.Example_5fd6d1e8e99d32826a97_AuxiliaryLemmas ====
/- Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file was automatically generated by Codex.
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Trilinear smoothing inequality in two dimensions

Task 1: Theorem 5 of https://arxiv.org/abs/2008.10140v2.
The development follows logical dependency order through Lemmas 3.1-3.3,
the localized estimate (3.2), interpolation, Sobolev summation, and duality.
The final result is `Auto.smoothing_theorem5`, with the literal form (1.9)
and the exact Sobolev weights printed after (1.10).
-/
@[expose] public section
namespace Auto
open MeasureTheory
open FourierTransform
open scoped FourierTransform ContDiff
/-- The multiplicative difference used in Section 3.2, Lemma 3.1 of
arXiv:2008.10140v2. This is a product with a translated function, not a derivative. -/
def smoothingMultiplicativeDifference {E : Type*} [Add E]
    (f : E → ℂ) (s : E) : E → ℂ :=
  fun x => f (x + s) * star (f x)
/-- The energy of the restricted L² vector equals the mass of its frequency
window, as used in the concluding norm bound of Lemma 3.1. -/
axiom smoothing_frequencyRestriction_norm_sq
    {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f : E → ℂ} (hf : MemLp f 2 μ) {s : Set E} (hs : MeasurableSet s) :
    ‖(hf.indicator (/- proof-bridge:5b4726486e6e752f5921039c -/ hs).nullMeasurableSet).toLp (s.indicator f)‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 ∂μ

/-- The equality in the final display of Lemma 3.1: the multiplicative-difference
energy on the centered ball is the spectral-pair energy at distance at most R. -/
axiom smoothing_fourierDifference_ball_energy
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) (R : ℝ) :
    (∫ s, ∫ ξ in Metric.closedBall (0 : E) R,
      ‖(𝓕 (smoothingMultiplicativeDifference (⇑f) s) : E → ℂ) ξ‖ ^ 2) =
      ∫ η, ‖(𝓕 f : Lp (α := E) ℂ 2 volume) η‖ ^ 2 *
        ∫ ξ in Metric.closedBall η R, ‖(𝓕 f : Lp (α := E) ℂ 2 volume) ξ‖ ^ 2

/-- The weighted frequency-ball energy is integrable. This supplies the
integrability hypothesis of `smoothing_exists_large_window` without assuming
convergence of the iterated energy integral in Lemma 3.1. -/
axiom smoothing_integrable_ball_energy
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure E} [SFinite μ]
    {w : E → ℝ} (hw : Integrable w μ) (R : ℝ) :
    Integrable (fun x => w x * ∫ y in Metric.closedBall x R, w y ∂μ) μ
/-- The inequality in the final display of Lemma 3.1: total spectral mass
multiplied by the supremum of the spectral mass in a ball bounds the energy. -/
theorem smoothing_fourierDifference_energy_le_ball_mass
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) (R : ℝ) :
    (∫ s, ∫ ξ in Metric.closedBall (0 : E) R,
      ‖(𝓕 (smoothingMultiplicativeDifference (⇑f) s) : E → ℂ) ξ‖ ^ 2) ≤
      ‖f‖ ^ 2 * sSup (Set.range (fun c : E =>
        ∫ ξ in Metric.closedBall c R, ‖(𝓕 f : Lp (α := E) ℂ 2 volume) ξ‖ ^ 2)) := by
  let w : E → ℝ := fun ξ => ‖(𝓕 f : Lp (α := E) ℂ 2 volume) ξ‖ ^ 2
  have hw : Integrable w volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 f)).aestronglyMeasurable).mp (Lp.memLp (𝓕 f))
  have hwpos : ∀ᵐ ξ ∂volume, 0 ≤ w ξ := Filter.Eventually.of_forall fun ξ => sq_nonneg _
  have hb : BddAbove (Set.range (fun c : E => ∫ ξ in Metric.closedBall c R, w ξ)) := by
    refine ⟨∫ ξ, w ξ, ?_⟩
    rintro y ⟨c, rfl⟩
    exact setIntegral_le_integral hw hwpos
  have hm : (∫ ξ, w ξ) = ‖f‖ ^ 2 := by
    have h := smoothing_frequencyRestriction_norm_sq (Lp.memLp (𝓕 f)) MeasurableSet.univ
    simpa only [Set.indicator_univ, Lp.toLp_coeFn, Measure.restrict_univ,
      Lp.norm_fourier_eq] using h.symm
  rw [smoothing_fourierDifference_ball_energy]
  change (∫ η, w η * ∫ ξ in Metric.closedBall η R, w ξ) ≤
    ‖f‖ ^ 2 * sSup (Set.range (fun c : E => ∫ ξ in Metric.closedBall c R, w ξ))
  rw [← hm, ← integral_mul_const]
  apply integral_mono_ae (smoothing_integrable_ball_energy hw R) (hw.mul_const _)
  filter_upwards [hwpos] with η hη
  exact mul_le_mul_of_nonneg_left (le_csSup hb (Set.mem_range_self η)) hη

end Auto
end
