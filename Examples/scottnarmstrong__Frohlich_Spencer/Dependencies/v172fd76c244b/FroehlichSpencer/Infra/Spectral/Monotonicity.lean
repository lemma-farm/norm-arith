/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.MinMax
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Sorted
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.QuadForm
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Shift invariance and Loewner monotonicity of eigenvalue counts

Shift invariance `N(E, H + t) = N(E - t, H)` (Fröhlich–Spencer (1983), Appendix C uses
`N(E, v) = N(0, v - E)`) and monotonicity of the counting functions and sorted eigenvalues under
positive semidefinite perturbations; in particular raising a diagonal potential lowers the counts.
-/
@[expose] public section
open Matrix Finset ComplexOrder
namespace FroehlichSpencer.Infra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}
end FroehlichSpencer.Infra
