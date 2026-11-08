/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v28afaa9d8af8.FroehlichSpencer.Infra.Resolvent.Complex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Decoupled finite-volume resolvents

This generic block decomposition is motivated by Fröhlich–Spencer (1983),
equations (2.10)–(2.13), pp. 159–160. No lattice or model-specific operator
is introduced here.
-/
public section
namespace FroehlichSpencer
namespace Matrix
end Matrix
end FroehlichSpencer
