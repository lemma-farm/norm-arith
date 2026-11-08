/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiDiagramMultiBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiChainBound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chain majorant with general exponents

The chain diagram of `I(Ψ³)Ψ` is dominated by
`(s₃(z,w) + s₃(0,w)) s_{1+α}(u,w) · (s_{4+γ}(z',v) + s_{4+γ}(0,v) + 2 s_{4+γ}(u',v)) s_{2+β}(w,v)`
(`s_a(c, w) = s(c - w)^(-a)`), which has the three exponents `α` (outer covariance), `β` (loss in
`Q²`) and `γ` (the covariance next to `δK(z', v)`) in place of `0, δ, 0`.  For `u = z, u' = z'`
(chaos-two pairing) or `u = z', u' = z` (secondary pairing) its double integral is bounded by
`C (s(z - z')^(-η) + s(z)^(-η) + s(z')^(-η))` with `η = α + β + γ`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- The chain majorant with exponents `α, β, γ`. -/
def i3PsiChainMajorant (α β γ : ℝ) (z z' u u' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
    ((singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v + 2 * singularPow (4 + γ) u' v) *
      singularPow (2 + β) w v)
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
