module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.ClassicalGradient
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth functions on bounded Sobolev domains

This file packages globally `C¹` scalar functions as representative-level
`W^{1,p}` functions on bounded measurable domains. Compact support is not
required: continuity on the compact closure of the domain supplies uniform
bounds for the function and each coordinate of its classical gradient.

The stored weak gradient is exactly `classicalGradient`, so later smooth
approximation arguments can use the same gradient API as the quantitative
regularity estimates.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
namespace W1pFunction
end W1pFunction
end PDE
