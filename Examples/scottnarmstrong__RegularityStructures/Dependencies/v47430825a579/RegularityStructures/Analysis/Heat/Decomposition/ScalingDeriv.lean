/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Support
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.SupportBound
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.SingularKernel
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.RegularisingDecomposition
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scaling of the derivatives of the heat shells

The `J`-derivative of the `n`-th heat shell is that of the zeroth shell at the dilated point, times
`(2^n)^{3 + |J|_𝔰}` (`lineIter_coordDir_heatShell`); mixed derivatives of a function of `x - y`
(`kernelDeriv_sub`).

Source: [Hai14, Lemma 5.5].
-/
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
