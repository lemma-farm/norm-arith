/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Scaled
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Vanishing monomial moments of the modified shells

`∫ z^k annShell N n z dz = 0` for all `n` and every multi-index `k` with `|k|_𝔰 < N`
(`integral_monomial_mul_annShell`): the moments of `annShell N n` are those of
`annKernel0 N`, rescaled by `2^{-(2 + |k|_𝔰) n}`, and the choice of `ψ` makes the moments of
`annKernel0 N` vanish.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5 (Assumption 5.4).
-/
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
