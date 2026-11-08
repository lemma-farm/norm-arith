/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Causal.Moment
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.SingularKernel
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Scaled
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Non-anticipativity of the causal decomposition

`annShellC N n z = 0` and `annRemainderC N z = 0` for `z.1 ≤ 0`
(`annShellC_eq_zero_of_nonpos`, `annRemainderC_eq_zero_of_nonpos`), and the same for every
iterated directional derivative (`lineIter_eq_zero_of_nonpos`, `lineIter_annShellC_eq_zero`,
`lineIter_annRemainderC_eq_zero`, in particular along `multiDirs k`).  This is the non-anticipativity
required in [Hai14, Theorem 7.1] and [Hai14, Lemma 7.7].

Source: Hairer, arXiv:1303.5113v4, Section 7.
-/
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
