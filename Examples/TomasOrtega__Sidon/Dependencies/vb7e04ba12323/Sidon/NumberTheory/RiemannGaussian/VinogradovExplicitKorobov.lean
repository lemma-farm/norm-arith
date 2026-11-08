module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.NumberTheory.Bertrand
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.VinogradovExplicitKorobov
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel
end
end RiemannGaussian.VinogradovExplicitKorobov
