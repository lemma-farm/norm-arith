/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DifferenceTables
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI3PsiDifferenceAlgebra
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The second difference of the chaos kernels of `I(Ψ²) Ψ²`: algebra

Write `T_z = (Q_{aa}(z), Q_{ab}(z), Q_{ba}(z), Q_{bb}(z))` for the table of cross covariances at a
point `z`, and `D(t₁, t₂, t₃, t₄) = ∏ tᵢ.a - ∏ tᵢ.b - ∏ tᵢ.c + ∏ tᵢ.d` for the mixed second difference
of a product of tables.  With `c₀₂ = Q(w - w')`, `c₀₃ = Q(w - y')`, `c₁₂ = Q(y - w')`,
`c₁₃ = Q(y - y')` the second difference of the chaos-`4` kernel
`4 c₀₂² c₁₃² + 4 c₀₃² c₁₂² + 16 c₀₂ c₀₃ c₁₂ c₁₃` is
`4 D(T₀₂,T₀₂,T₁₃,T₁₃) + 4 D(T₀₃,T₀₃,T₁₂,T₁₂) + 16 D(T₀₂,T₀₃,T₁₂,T₁₃)`; that of the chaos-`2` kernel
`16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)` is `16 D(T₀₁,T₂₃,T₀₂,T₁₃) + 16 D(T₀₁,T₂₃,T₀₃,T₁₂)`
(with the tables `(a, a, d, d)` for `c₀₁` and `(a, d, a, d)` for `c₂₃`).

If the tables satisfy the bound data `Bd μ (A pᵢ) (2 qᵢ)`, the mixed second differences are bounded by
`65536 A⁴ μ²` times the sums `i2Psi2Mon4` and `i2Psi2Mon2` of eight monomials in the `pᵢ`, `qᵢ`, in
which exactly one factor `pᵢ` is replaced by `pᵢ qᵢ²`.
-/
@[expose] public section
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
public section
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
