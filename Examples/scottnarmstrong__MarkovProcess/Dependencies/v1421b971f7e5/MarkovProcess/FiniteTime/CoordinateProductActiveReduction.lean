/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.CoordinateProductNormalization
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Restricting normalized coordinate products to active coordinates

This file enumerates the active coordinates of a normalized `CoordinateProductTerm`, extracts
their genuine `C₀` factors, and proves that evaluation factors through the corresponding
coordinate restriction.  The restricting function is definitionally the same path operation as
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding factors)` when that finite-time API is in
scope.

If there are no active coordinates, the reduced index type is `Fin 0` and the empty scalar
product is one.  No constant-one element of `C₀` is constructed.  This is purely algebraic
finite-product infrastructure: it involves no measure and no kernel.
-/
open scoped CompactlySupported ZeroAtInfty BigOperators
namespace MarkovProcess.PiContinuousMap
variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]
end MarkovProcess.PiContinuousMap
