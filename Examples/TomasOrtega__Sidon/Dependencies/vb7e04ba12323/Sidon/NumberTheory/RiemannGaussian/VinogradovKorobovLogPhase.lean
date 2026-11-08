module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.EtaCubicBoundaryTest
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.VinogradovKorobovLogPhase
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators Interval
def remainder (k : ℕ) (x : ℝ) : ℝ :=
  ∫ u : ℝ in 0..x, u ^ k / (1 + u)
end
end RiemannGaussian.VinogradovKorobovLogPhase
