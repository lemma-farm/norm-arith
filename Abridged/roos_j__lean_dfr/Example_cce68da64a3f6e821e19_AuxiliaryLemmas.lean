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

-- ==== Examples.roos_j__lean_dfr.Examples.Example_cce68da64a3f6e821e19_AuxiliaryLemmas ====
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

set_option linter.unusedVariables false in
axiom _root_.Auto.smoothing_memLp_modulation.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E]
  [inst_2 : BorelSpace E] [inst_3 : InnerProductSpace ℝ E] [inst_4 : FiniteDimensional ℝ E]
  {f : E → ℂ},
  MeasureTheory.MemLp f 2 MeasureTheory.MeasureSpace.volume →
    ∀ (a : E),
      MeasureTheory.MemLp (fun (x : E) ↦ (Real.fourierChar : ℝ → Circle) (Inner.inner ℝ a x) • f x)
        2 MeasureTheory.MeasureSpace.volume
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

/-- Translation isometry used in the first Fourier computation of Lemma 3.1. -/
noncomputable def smoothingTranslationL2
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    Lp (α := E) ℂ 2 volume →ₗᵢ[ℂ] Lp (α := E) ℂ 2 volume :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a) (measurePreserving_add_right volume a)

/-- The cutoff chosen in the first sentence of Lemma 3.2's proof. Its transition
intervals give compact support strictly inside (-1,1) and an integer partition. -/
noncomputable def smoothingPartitionCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x + 3 / 2) - Real.smoothTransition (2 * x - 1 / 2)

/-- The centered spectral piece whose inverse Fourier transform is h_n in
Lemma 3.2(2). Demodulation moves the selected window to the origin. -/
noncomputable def smoothingPieceSpectrum (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (n : ℤ) (ξ : ℝ) : ℂ :=
  (smoothingPartitionCutoff (ξ / R) : ℂ) *
    (𝓕 f : Lp (α := ℝ) ℂ 2 volume) (ξ - n * R)

set_option linter.unusedVariables false in
axiom _root_.Auto.smoothingPieceSpectrum_memLp : ∀ (f : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume)) (R : ℝ) (n : ℤ),
  MeasureTheory.MemLp (Auto.smoothingPieceSpectrum f R n) 2 MeasureTheory.MeasureSpace.volume
/-- The L² class of the smooth piece h_n from Lemma 3.2. -/
noncomputable def smoothingPieceL2 (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (n : ℤ) : Lp (α := ℝ) ℂ 2 volume :=
  𝓕⁻ ((smoothingPieceSpectrum_memLp f R n).toLp _)

set_option linter.unusedVariables false in
/-- The individual L² bound for h_n in Lemma 3.2(2), with constant one. -/
theorem smoothingPieceL2_norm_le (f : Lp (α := ℝ) ℂ 2 volume)
    (R : ℝ) (n : ℤ) 
    (h_Auto_smoothingPartitionCutoff_bounds : ∀ (x : ℝ), 0 ≤ Auto.smoothingPartitionCutoff x ∧ Auto.smoothingPartitionCutoff x ≤ 1)
    (h_Auto_smoothingPieceL2_fourier : ∀ (f : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume)) (R : ℝ) (n : ℤ),
      (↑(↑(FourierTransform.fourier (Auto.smoothingPieceL2 f R n)) :
              ℝ →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
          ℝ → ℂ) =ᵐ[MeasureTheory.MeasureSpace.volume]
        Auto.smoothingPieceSpectrum f R n)
    (h_Auto_smoothingTranslationL2_coe : ∀ {E : Type} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : BorelSpace E]
      [inst_3 : InnerProductSpace ℝ E] [inst_4 : FiniteDimensional ℝ E] (a : E)
      (f : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume)),
      (↑(↑((Auto.smoothingTranslationL2 a :
                    ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume) →
                      ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume))
                  f) :
              E →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
          E → ℂ) =ᵐ[MeasureTheory.MeasureSpace.volume]
        fun (x : E) ↦ (↑(↑f : E →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) : E → ℂ) (x + a))
    : ‖smoothingPieceL2 f R n‖ ≤ ‖f‖ := by
  have hbound : ‖(𝓕 (smoothingPieceL2 f R n) : Lp (α := ℝ) ℂ 2 volume)‖ ≤
      ‖smoothingTranslationL2 (-(n : ℝ) * R) (𝓕 f)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h_Auto_smoothingPieceL2_fourier f R n,
      h_Auto_smoothingTranslationL2_coe (-(n : ℝ) * R) (𝓕 f)] with ξ hξ ht
    rw [hξ, ht, smoothingPieceSpectrum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h_Auto_smoothingPartitionCutoff_bounds _).1]
    simp only [sub_eq_add_neg, neg_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h_Auto_smoothingPartitionCutoff_bounds _).2
  simpa only [Lp.norm_fourier_eq, LinearIsometry.norm_map] using hbound

end Auto
end
