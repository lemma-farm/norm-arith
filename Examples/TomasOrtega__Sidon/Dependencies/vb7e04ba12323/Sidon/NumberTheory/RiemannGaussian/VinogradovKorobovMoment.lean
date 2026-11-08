module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Data.List.Permutation
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianCentering
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianKernel
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianResonance
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovMomentReduction
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.VinogradovKorobovMoment
noncomputable section
open UnitAddTorus RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovMomentReduction
open RiemannGaussian.VinogradovKorobovBilinearPhase
open scoped BigOperators
end
end RiemannGaussian.VinogradovKorobovMoment
