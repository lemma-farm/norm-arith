/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.MetricSpace.CoveringNumbers
-- Modules re-exported to keep the pre-module-system import visibility.
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
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Data.List.Enum
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
@[expose] public section
/-!

# Basic definitions for this project

-/
namespace Spherical
open Filter MeasureTheory Set Topology ENNReal
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
/- `d`-dimensional real Euclidean space. -/
scoped notation "ℝ^" d:arg => EuclideanSpace ℝ (Fin d)
section SphericalMaximal
/-- `d`-dimensional Euclidean unit sphere -/
abbrev unitSphere (d : ℕ) := Metric.sphere (0 : ℝ^d) 1
/-- Normalized surface measure on the Euclidean unit sphere. -/
def unitSphereMeasure (d : ℕ) : Measure (unitSphere d) := by
  let μ : Measure (Metric.sphere (0 : ℝ^d) 1) := volume.toSphere
  exact (μ univ)⁻¹ • μ
/-- Spherical average of `f` centered at `x` with radius `t`. -/
def sphericalAverage {d : ℕ} (t : ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, f (x + t • (y : ℝ^d)) ∂(unitSphereMeasure d)
/-- The spherical maximal function restricted to a set of radii `E`. -/
def restrictedSphericalMaximal {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal :=
  ⨆ t ∈ E ∩ Ioi 0, ENNReal.ofReal ‖sphericalAverage t f x‖
@[inherit_doc restrictedSphericalMaximal]
abbrev M {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal := restrictedSphericalMaximal E f x
end SphericalMaximal
section FractalDimensions
/-- The image of a dilation set in logarithmic coordinates. -/
def logDilationSet (E : Set ℝ) : Set ℝ :=
  {u | ∃ r : Ioi (0 : ℝ), r.1 ∈ E ∧ Real.log r.1 / Real.log 2 = u}
/-- A closed ball in the logarithmic metric on the positive radii. -/
def logBall (c : Ioi (0 : ℝ)) (r : ℝ≥0) : Set ℝ :=
  {t | 0 < t ∧ |Real.log t / Real.log 2 - Real.log c.1 / Real.log 2| ≤ r}
/-- The minimum number of logarithmic balls of radius `δ` needed to cover `E`. -/
def entropyNumber (E : Set ℝ) (δ : ℝ≥0) : ENat :=
  Metric.externalCoveringNumber δ (logDilationSet E)
@[inherit_doc entropyNumber]
abbrev N (E : Set ℝ) (δ : ℝ≥0) : ENat := entropyNumber E δ
/-- The upper Minkowski dimension of a dilation set. -/
def upperMinkowskiExponent (E : Set ℝ) : ℝ :=
  limsup (fun r : NNReal ↦ ENNReal.log (⨆ c : Ioi (0 : ℝ),
      N (E ∩ (logBall c 1)) r) / (Real.log ((r : ℝ)⁻¹) : EReal))
    (𝓝[>] 0) |>.toReal
@[inherit_doc upperMinkowskiExponent]
abbrev β (E : Set ℝ) : ℝ := upperMinkowskiExponent E
/-- The Legendre--Assouad function `ν♯` of a dilation set. -/
def legendreAssouadFunction (E : Set ℝ) (ρ : ℝ) : ℝ :=
  limsup (fun r : NNReal ↦ ENNReal.log (⨆ c : Ioi 0, ⨆ R : Icc r 1,
      (R.1 : ℝ≥0∞) ^ (-ρ) * N (E ∩ (logBall c R)) r) / (Real.log (r⁻¹) : EReal))
    (𝓝[>] 0) |>.toReal
@[inherit_doc legendreAssouadFunction]
scoped notation "ν♯" => legendreAssouadFunction
/-- Generalized inverse of an increasing function. -/
def generalizedInverse (f : ℝ → ℝ) (s : ℝ) : ℝ := sSup {ρ : ℝ | 0 ≤ ρ ∧ f ρ ≤ s}
@[inherit_doc generalizedInverse]
scoped notation f "†" => generalizedInverse f
end FractalDimensions
namespace RestrictedDilations
section SpecialDilationSets
end SpecialDilationSets
end RestrictedDilations
namespace PowerWeights
open RestrictedDilations
end PowerWeights
end
end Spherical
