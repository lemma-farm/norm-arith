/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.Moments
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Semigroup.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The auxiliary regularising semigroup on `ℝ⁴`

`parabolicSemigroup` is the `RegularisingSemigroup ParabolicSpace volume` with kernel
`Q_t(x, y) = q_t(x - y)`, `q_t = parabolicKernel t`, scaling order `ℓ = 4` and size
`d(y, x) = ‖y - x‖_𝔰`. It is used *only* to measure regularity; it is not the causal heat kernel
of the PDE. This is the setting of [Hos25, Definition 2.6 (i), (iii), Example 2.7]
(arXiv:2310.07396v2).

* the semigroup property follows from the 1D ones by Fubini
  (`integral_quarticKernel_mul_quarticKernel`, `integral_heatKernel1D_mul_heatKernel1D`);
* the moment bounds from `RegularityStructures.Analysis.Kernel.Moments`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
