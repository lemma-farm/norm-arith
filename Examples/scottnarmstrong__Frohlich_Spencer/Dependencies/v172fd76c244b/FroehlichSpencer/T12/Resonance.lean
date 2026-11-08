/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.Hamiltonian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.HamiltonianHermitian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.DirichletLaplacian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.ConfigurationMeasure
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.BoundedDensityLaw
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.GaussianLaw
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Wegner.Resonance
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Lattice.Kernel
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
Internal lemmas for the resonance event `Res(Λ, E, κ) = {v | dist(spec H_Λ(v), E) ≤ κ}` of the
finite-volume Hamiltonian: measurability, locality, the shift `H_Λ = A_Λ + diag v + 2ν`, the
bounded-density Wegner bound, the Gershgorin bound, and the two combined branch estimates
(Fröhlich–Spencer (1983), Appendix C, Fröhlich–Spencer (1983)).
-/
@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal Matrix Pointwise
namespace FroehlichSpencer.T12
instance (γ : ℝ) (hγ : 0 < γ) : IsProbabilityMeasure (gaussianLaw γ hγ) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
end FroehlichSpencer.T12
