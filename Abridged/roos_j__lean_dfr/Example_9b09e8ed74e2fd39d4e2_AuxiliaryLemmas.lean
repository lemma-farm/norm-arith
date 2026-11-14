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

-- ==== Examples.roos_j__lean_dfr.Examples.Example_9b09e8ed74e2fd39d4e2_AuxiliaryLemmas ====
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

/-- Multiplication by the Fourier character preserves L²; used in the first
unnumbered display of the proof of Lemma 3.1. -/
axiom smoothing_memLp_modulation
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℂ} (hf : MemLp f 2 volume) (a : E) :
    MemLp (fun x => Real.fourierChar (inner ℝ a x) • f x) 2 volume
/-- The modulation isometry underlying the Fourier computation in Lemma 3.1. -/
noncomputable def smoothingModulationL2
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    Lp (α := E) ℂ 2 volume →ₗᵢ[ℂ] Lp (α := E) ℂ 2 volume where
  toFun f := (smoothing_memLp_modulation (Lp.memLp f) a).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(smoothing_memLp_modulation (Lp.memLp (f + g)) a).coeFn_toLp,
      Lp.coeFn_add ((smoothing_memLp_modulation (Lp.memLp f) a).toLp _)
        ((smoothing_memLp_modulation (Lp.memLp g) a).toLp _),
      (smoothing_memLp_modulation (Lp.memLp f) a).coeFn_toLp,
      (smoothing_memLp_modulation (Lp.memLp g) a).coeFn_toLp,
      Lp.coeFn_add f g] with x hfg hadd hf hg hfg'
    simp only [Pi.add_apply, hfg, hadd, hf, hg, hfg', smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(smoothing_memLp_modulation (Lp.memLp (c • f)) a).coeFn_toLp,
      Lp.coeFn_smul c ((smoothing_memLp_modulation (Lp.memLp f) a).toLp _),
      (smoothing_memLp_modulation (Lp.memLp f) a).coeFn_toLp,
      Lp.coeFn_smul c f] with x hcf hmul hf hcf'
    simp only [Pi.smul_apply] at hmul hcf'
    simp only [RingHom.id_apply]
    rw [hcf, hmul, hf, hcf']
    exact smul_comm _ _ _
  norm_map' f := by
    change ‖(smoothing_memLp_modulation (Lp.memLp f) a).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (by fun_prop) (by fun_prop) (Filter.Eventually.of_forall fun x =>
      by simp)

/-- The inequality in the final display of Lemma 3.1: total spectral mass
multiplied by the supremum of the spectral mass in a ball bounds the energy. -/
axiom smoothing_fourierDifference_energy_le_ball_mass
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Lp (α := E) ℂ 2 volume) (R : ℝ) :
    (∫ s, ∫ ξ in Metric.closedBall (0 : E) R,
      ‖(𝓕 (smoothingMultiplicativeDifference (⇑f) s) : E → ℂ) ξ‖ ^ 2) ≤
      ‖f‖ ^ 2 * sSup (Set.range (fun c : E =>
        ∫ ξ in Metric.closedBall c R, ‖(𝓕 f : Lp (α := E) ℂ 2 volume) ξ‖ ^ 2))
/-- The cutoff chosen in the first sentence of Lemma 3.2's proof. Its transition
intervals give compact support strictly inside (-1,1) and an integer partition. -/
noncomputable def smoothingPartitionCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x + 3 / 2) - Real.smoothTransition (2 * x - 1 / 2)

/-- The high-mass index set in Lemma 3.2's proof. The interval has length R
and intersects the support of the corresponding scaled partition cutoff. -/
def smoothingHighMassIndices (w : ℝ → ℝ) (R ρ : ℝ) : Set ℤ :=
  {n | ∃ a : ℝ,
    (Set.Icc a (a + R) ∩ Function.support
      (fun ξ => smoothingPartitionCutoff (ξ / R + n))).Nonempty ∧
    ρ * (∫ ξ, w ξ) ≤ ∫ ξ in Set.Icc a (a + R), w ξ}

/-- The finite multiplier defining the sharp part in Lemma 3.2. -/
noncomputable def smoothingSharpMultiplier (R : ℝ) (S : Finset ℤ) (ξ : ℝ) : ℝ :=
  ∑ n ∈ S, smoothingPartitionCutoff (ξ / R + n)

/-- The sharp Fourier multiplier acts on every L² input. -/
axiom smoothing_memLp_sharpMultiplier (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (S : Finset ℤ) :
    MemLp (fun ξ => (smoothingSharpMultiplier R S ξ : ℂ) *
      (𝓕 f : Lp (α := ℝ) ℂ 2 volume) ξ) 2 volume
/-- The sharp part defined in the displayed formulas of Lemma 3.2's proof. -/
noncomputable def smoothingSharpPart (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (S : Finset ℤ) : Lp (α := ℝ) ℂ 2 volume :=
  𝓕⁻ ((smoothing_memLp_sharpMultiplier f R S).toLp _)
/-- The flat part in the same source display. -/
noncomputable def smoothingFlatPart (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (S : Finset ℤ) : Lp (α := ℝ) ℂ 2 volume :=
  f - smoothingSharpPart f R S

/-- The flat part's L² bound in Lemma 3.2(1). -/
axiom smoothingFlatPart_norm_le (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (S : Finset ℤ) : ‖smoothingFlatPart f R S‖ ≤ ‖f‖

/-- The flat Fourier mass in any radius-R ball is at most twice the source
interval threshold. This handles the radius versus interval-length conversion. -/
axiom smoothingFlatPart_ball_mass (f : Lp (α := ℝ) ℂ 2 volume)
    (R c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (S : Finset ℤ)
    (hselect : ∀ n : ℤ, n ∈ S ↔ n ∈ smoothingHighMassIndices
      (fun ξ => ‖(𝓕 f : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2) R ρ) :
    (∫ ξ in Metric.closedBall c R,
      ‖(𝓕 (smoothingFlatPart f R S) : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2) ≤
      2 * ρ * (∫ ξ, ‖(𝓕 f : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2)
/-- Equation (3.25) of Lemma 3.2(3), with uniform constant 2. The source's
high-mass interval contradiction is applied to the maximal-ball energy bound
proved in Lemma 3.1, avoiding an unnecessary second orthogonal projection. -/
theorem smoothingFlatPart_energy_bound (f : Lp (α := ℝ) ℂ 2 volume) (R : ℝ) {ρ : ℝ} (hρ : 0 <
    ρ) (S : Finset ℤ)
    (hselect :
      f ≠ 0 → ∀ n : ℤ, n ∈ S ↔ n ∈ smoothingHighMassIndices (fun ξ => ‖(𝓕 f : Lp (α := ℝ) ℂ 2
        volume) ξ‖ ^ 2) R ρ) :
    (∫ s : ℝ, ∫ ξ in Metric.closedBall (0 : ℝ) R,
      ‖(𝓕 (smoothingMultiplicativeDifference (⇑(smoothingFlatPart f R S)) s) : ℝ → ℂ) ξ‖ ^ 2) ≤
      2 * ρ * ‖f‖ ^ 4 := by
  by_cases hfzero : f = 0
  · have hgzero : smoothingFlatPart f R S = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hfzero, norm_zero] using smoothingFlatPart_norm_le f R S)
        (norm_nonneg _)
    have he := smoothing_fourierDifference_energy_le_ball_mass (smoothingFlatPart f R S) R
    rw [hgzero] at he ⊢
    simpa only [hfzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero] using he
  have hm : (∫ ξ, ‖(𝓕 f : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2) = ‖f‖ ^ 2 := by
    have h := smoothing_frequencyRestriction_norm_sq (Lp.memLp (𝓕 f)) MeasurableSet.univ
    simpa only [Set.indicator_univ, Lp.toLp_coeFn, Measure.restrict_univ,
      Lp.norm_fourier_eq] using h.symm
  have hball (c : ℝ) : (∫ ξ in Metric.closedBall c R,
      ‖(𝓕 (smoothingFlatPart f R S) : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2) ≤ 2 * ρ * ‖f‖ ^ 2 := by
    simpa only [hm] using smoothingFlatPart_ball_mass f R c hρ S (hselect hfzero)
  have hs : sSup (Set.range (fun c : ℝ => ∫ ξ in Metric.closedBall c R,
      ‖(𝓕 (smoothingFlatPart f R S) : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2)) ≤ 2 * ρ * ‖f‖ ^ 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨c, rfl⟩
    exact hball c
  calc
    _ ≤ ‖smoothingFlatPart f R S‖ ^ 2 * sSup (Set.range (fun c : ℝ =>
        ∫ ξ in Metric.closedBall c R,
          ‖(𝓕 (smoothingFlatPart f R S) : Lp (α := ℝ) ℂ 2 volume) ξ‖ ^ 2)) :=
      smoothing_fourierDifference_energy_le_ball_mass (smoothingFlatPart f R S) R
    _ ≤ ‖smoothingFlatPart f R S‖ ^ 2 * (2 * ρ * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ ≤ ‖f‖ ^ 2 * (2 * ρ * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (smoothingFlatPart_norm_le f R S) 2) (by positivity)
    _ = _ := by ring
end Auto
end
