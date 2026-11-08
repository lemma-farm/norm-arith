/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Regularity
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Resolvent
import Mathlib
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Resolvent norm equals inverse spectral distance

For a Hermitian matrix `H`, `H - z • 1` is invertible iff `z` is not an eigenvalue, and the
L² operator norm of its inverse is the reciprocal of the distance from `z` to the spectrum.

This links the resolvent bound `‖G‖ ≤ e^{√d}` of Fröhlich–Spencer (1983) with the spectral
condition `dist(spec H, E) ≥ e^{-√d}` (Condition A(c), Fröhlich–Spencer (1983)).
-/
@[expose] public section
open scoped Matrix.Norms.L2Operator
namespace FroehlichSpencer.Infra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
end FroehlichSpencer.Infra
