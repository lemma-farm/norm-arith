/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Support
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.SingularKernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Derivative scaling of the heat shells

For a list `J` of coordinate indices (so `J.map coordDir` is a list of coordinate directions),
`D_J (heatShell n) (z) = (2^n)^{3 + |J|_𝔰} (D_J (heatShell 0)) (2^n z)`, and the mixed derivatives
`kernelDeriv k l (fun x y => h (x - y))` reduce to `(-1)^{|l|} D^{k,l} h (x - y)`.
-/
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
