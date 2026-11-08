/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.FiniteProductCompactSupportApproximation
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit coordinate-product normal forms

This file replaces abstract membership in the coordinate `C₀` algebra by a concrete finite
sum of finite products.  Factors are stored in lists, so the normal form can subsequently be
consumed by recursion (for example, by iterated kernel integration).  The empty factor list is
the constant function `1`; in particular the representation treats constants and an empty
coordinate type without exceptional cases.
-/
open scoped CompactlySupported ZeroAtInfty
namespace MarkovProcess.PiContinuousMap
variable {I α : Type*} [TopologicalSpace α]
end MarkovProcess.PiContinuousMap
