/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramDiffBound
public import Mathlib.Algebra.Order.Star.Real
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI3PsiDifferenceAlgebra
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The `2 × 2` tables of cross covariances: uniform bound data

The bound data `Bd μ P Q` of the tables `(a, b, c, d)`, `(a, a, d, d)`, `(a, d, a, d)` of cross
covariances, `μ = (max ε ε')^θ`, enter the second difference of the chaos kernels of `I(Ψ²) Ψ²`
with weights both at `s(z)` and at `s(-z)` (the orientation of the kernel increments). The bound
data are therefore used in a uniform form, through the monotonicity of `Bd` in `P` and `Q`
(`i2Psi2DiffTableBd_mono`).
-/
public section
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
