/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.MildTime
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Mild solutions with smooth data are smooth

Let `G` be a smooth nonlinearity, `u₀` a smooth function on `T³` and `u` a continuous mild solution
of `∂_t u = Δu + G(t, x, u)` on `[0, T]`. Then the lift `(t, y) ↦ u(t, torusProj y)` is smooth on
`(0, T) × ℝ³` (`contDiffOn_of_isMildSolution`).

The proof is an induction on the order `n`, simultaneously for all smooth systems. A `C¹` function
on an open set is `C^{n+1}` when its derivative is `C^n`. The derivative of the lift is assembled
from the time derivative `Δu + G(t, x, u)` and the spatial partial derivatives
(`hasStrictFDerivAt_uncurry_coprod`); the spatial partial derivatives and the Laplacian are
components of mild solutions of the jet system and of the jet of the jet system, which are again
smooth systems, so the induction hypothesis applies to them.
-/
open scoped ContDiff
public section
open Set Filter Topology
namespace RegularityStructures.PDE
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
