module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.NumberTheory.LSeries.Deriv
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
open Complex Filter Topology
open scoped Classical
namespace RiemannGaussian
noncomputable section
end
end RiemannGaussian
