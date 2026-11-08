/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Lattice.Kernel
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.Existence
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.InfiniteVolumeRegularity
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Ergodic.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Lattice.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The lattice Green function

The infinite-volume Green function `G(z; x, y)(v)` on `ℤ^ν`, the unique square-summable solution of
`(-Δ + v - z) ψ = δ_y`, obtained from the generic theorem for `hoppingKernel ν` with potential
`v + 2ν`.

We prove the characterization, the bound `|G| ≤ 1/|Im z|`, shift covariance,
measurability in `v`, Combes–Thomas decay and the large-`t` asymptotics `it · G(it; y, y) → -1`.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/
@[expose] public section
open MeasureTheory Complex Filter Topology
namespace FroehlichSpencer.IDS
end FroehlichSpencer.IDS
