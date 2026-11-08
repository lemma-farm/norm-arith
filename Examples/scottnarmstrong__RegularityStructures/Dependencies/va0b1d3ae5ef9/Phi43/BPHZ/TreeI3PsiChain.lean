/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiSigma
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiTwoLevel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The diagrams with a `Q²`-link between the two integration variables

Let `δK(z, w) = K(z - w) - K(-w)`.  For `(u, u') = (z, z')` (the chaos-two pairing
`Q(w - z) Q(w - w̄)² Q(w̄ - z̄)`) and `(u, u') = (z', z)` (the secondary pairing
`Q(w - w̄)² Q(w - z̄) Q(w̄ - z)`), the double integral of
`δK(z, w) δK(z', w̄) Q(w - u) Q(w - w̄)² Q(w̄ - u')` is absolutely integrable and bounded by
`s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168 (secondary pairings: source gap, bounded by the
same lemmas).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
theorem SingularIntLe.congr_fun {f g : SpaceTime → ℝ} {X : ℝ} (h : ∀ w, f w = g w)
    (hf : SingularIntLe f X) : SingularIntLe g X := by
  have : f = g := funext h
  rwa [this] at hf
end RegularityStructures
end
