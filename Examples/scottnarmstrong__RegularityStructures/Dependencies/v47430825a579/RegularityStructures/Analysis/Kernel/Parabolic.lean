/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Pi
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The parabolic kernel on `ℝ × ℝ³`

`parabolicKernel t (s, x) = heatKernel1D t s * ∏ᵢ quarticKernel t (xᵢ)`: the tensor product of the
1D heat kernel in time and three 1D quartic kernels in space. It is the fundamental solution of
`∂_t - ∂₀² + ∑ᵢ ∂ᵢ⁴` ([Hos25, Example 2.7] (arXiv:2310.07396v2), with the spatial bi-Laplacian
replaced by `∑ᵢ ∂ᵢ⁴`), and is *only* used as the auxiliary kernel measuring regularity.

We prove joint measurability, exact parabolic scaling
`q_t(z) = t^{-5/4} q_1(S^{t^{-1/4}} z)`, `∫ q_t = 1`, and integrability and the value of the weighted
integrals `∫ |g_t(z₀)| |z₀|^a ∏ᵢ |k_t(zᵢ)| |zᵢ|^{eᵢ} dz`, from which the moment bounds follow
(`RegularityStructures.Analysis.Kernel.Moments`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
