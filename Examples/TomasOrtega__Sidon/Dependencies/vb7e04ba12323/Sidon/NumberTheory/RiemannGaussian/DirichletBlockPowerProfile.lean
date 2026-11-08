module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletPowerCoefficients
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.LogarithmicDerivativeFamily
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.UniformDirichletPowerBound
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.DirichletBlockPowerProfile
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerCoefficients RiemannGaussian.DirichletDyadicBlocks
open RiemannGaussian.LogarithmicDerivativeFamily
end
end RiemannGaussian.DirichletBlockPowerProfile
