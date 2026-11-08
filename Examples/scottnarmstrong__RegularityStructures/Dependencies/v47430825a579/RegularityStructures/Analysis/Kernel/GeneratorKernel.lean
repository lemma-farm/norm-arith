/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorDeriv
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.TimeDeriv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The heat equation for the parabolic kernel

`kernelDerivs t a b₀ b₁ b₂ (s, x) = g_t^{(a)}(s) k_t^{(b₀)}(x₀) k_t^{(b₁)}(x₁) k_t^{(b₂)}(x₂)`
are the partial derivatives of `parabolicKernel t = kernelDerivs t 0 0 0 0`. We show that
differentiating along `timeDir` raises `a`, and along `spaceDir i` raises `bᵢ`, and deduce the
pointwise heat equation `∂_t q_t = L q_t`, `L = (4π²)⁻¹ ∂₀² - (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴`
(`parabolicTimeDeriv_eq`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
