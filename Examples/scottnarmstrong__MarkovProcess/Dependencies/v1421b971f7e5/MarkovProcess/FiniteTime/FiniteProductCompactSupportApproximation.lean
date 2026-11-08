/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.FiniteProductStoneWeierstrass
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compactly supported approximation on a finite product

This file upgrades compact-set Stone--Weierstrass approximation to a uniform approximation on the
whole product.  The key device is a product of one-coordinate compactly supported cutoffs.  Each
coordinate cutoff is one on the corresponding projection of the target's compact support.
-/
open Topology
open scoped CompactlySupported ZeroAtInfty
namespace MarkovProcess.PiContinuousMap
variable {I α : Type*} [Fintype I] [TopologicalSpace α]
end MarkovProcess.PiContinuousMap
