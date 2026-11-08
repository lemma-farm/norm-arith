/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.KernelCalculusBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integrals of the majorants for the renormalised convolution

Each of the four majorants in `abs_mul_sub_le_majorant` is integrable, with integral at most a
constant multiple of `ρ^(5-a₁-a₂)`, where `ρ = s(z)`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
