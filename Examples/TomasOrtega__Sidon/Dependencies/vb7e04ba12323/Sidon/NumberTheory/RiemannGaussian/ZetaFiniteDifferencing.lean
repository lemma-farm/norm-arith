module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Periodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.LogarithmicShiftPhase
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.ZetaFiniteDifferencing
noncomputable section
open Complex RiemannGaussian.LogarithmicShiftPhase
open scoped Classical
end
end RiemannGaussian.ZetaFiniteDifferencing
