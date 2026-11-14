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

-- ==== Examples.roos_j__lean_dfr.Examples.Example_5075df8af78f85f7de81_AuxiliaryLemmas ====
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

/-- Plancherel for the convergent Fourier integral of an L¹ ∩ L² function.
This bridges the raw Fourier integrals in Lemma 3.1 to the L² isometry. -/
axiom smoothing_integral_norm_sq_fourier
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℂ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    (∫ ξ, ‖(𝓕 f : E → ℂ) ξ‖ ^ 2) = ∫ x, ‖f x‖ ^ 2

/-- The correlation in Lemma 3.1 is integrable at every frequency. -/
axiom smoothing_integrable_fourierCorrelation
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) (ξ : E) :
    Integrable (fun η => (𝓕 f : Lp (α := E) ℂ 2 volume) (ξ + η) *
      star ((𝓕 f : Lp (α := E) ℂ 2 volume) η)) volume
/-- The correlation in Lemma 3.1 belongs to L² for almost every frequency;
Fubini applies because the product of the two spectral square norms is integrable. -/
axiom smoothing_ae_memLp_fourierCorrelation
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) :
    ∀ᵐ ξ ∂volume, MemLp (fun η =>
      (𝓕 f : Lp (α := E) ℂ 2 volume) (ξ + η) *
        star ((𝓕 f : Lp (α := E) ℂ 2 volume) η)) 2 volume
/-- Removing the unit phase expresses the correlation computation in Lemma 3.1
as a Fourier transform evaluated at the negative translation parameter. -/
axiom smoothing_fourier_multiplicativeDifference_norm
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) (s ξ : E) :
    ‖(𝓕 (smoothingMultiplicativeDifference (⇑f) s) : E → ℂ) ξ‖ =
      ‖(𝓕 (fun η => (𝓕 f : Lp (α := E) ℂ 2 volume) (ξ + η) *
        star ((𝓕 f : Lp (α := E) ℂ 2 volume) η)) : E → ℂ) (-s)‖
/-- The third unnumbered display of Lemma 3.1, interpreted almost everywhere
in frequency as required for arbitrary L² inputs: integration in the translation
parameter gives the squared spectral correlation. -/
theorem smoothing_integral_fourier_multiplicativeDifference_norm_sq
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) :
    ∀ᵐ ξ ∂volume,
      (∫ s, ‖(𝓕 (smoothingMultiplicativeDifference (⇑f) s) : E → ℂ) ξ‖ ^ 2) =
      ∫ η, ‖(𝓕 f : Lp (α := E) ℂ 2 volume) (ξ + η)‖ ^ 2 *
        ‖(𝓕 f : Lp (α := E) ℂ 2 volume) η‖ ^ 2 := by
  filter_upwards [smoothing_ae_memLp_fourierCorrelation f] with ξ hξ
  simp_rw [smoothing_fourier_multiplicativeDifference_norm]
  rw [integral_neg_eq_self (fun s =>
    ‖(𝓕 (fun η => (𝓕 f : Lp (α := E) ℂ 2 volume) (ξ + η) *
      star ((𝓕 f : Lp (α := E) ℂ 2 volume) η)) : E → ℂ) s‖ ^ 2) volume]
  rw [smoothing_integral_norm_sq_fourier
    (smoothing_integrable_fourierCorrelation f ξ) hξ]
  simp only [norm_mul, norm_star, mul_pow]

end Auto
end
