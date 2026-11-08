/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.LatticeLength
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.Hamiltonian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Lattice.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Lattice.Balls
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Multiscale basics: scales, site distance, thickening, singular sites

Internal definitions for the multiscale construction of Fröhlich–Spencer (1983), Sect. 2.
-/
@[expose] public section
namespace FroehlichSpencer.Multiscale
/-- Parameters of the multiscale construction (FS83 Sect. 2): the energy `E`, the singular
threshold `Nthr` (FS83 `N(E, δ)`, (2.2)) and the scale parameter `K₀` ((2.4)). -/
structure Params where
  E : ℝ
  Nthr : ℝ
  K₀ : ℝ
end FroehlichSpencer.Multiscale
end
