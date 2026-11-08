/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Integration.PolyCompat.Compat
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomial compatibility: injectivity and `Γ` on polynomials

Aggregator for `RegularityStructures.Abstract.Integration.PolyCompat`: the approximate identity for
functions of polynomial growth (`Approx`, `ApproxPoly`), injectivity of `τ ↦ (Q_t (· - x)^τ)_{t>0}`
(`polyReg_injective`, `Inject`), and for `M.IsPolyCompatible P` the injectivity of `Π_x` on
`P.subspace` and the formula for `Γ_{xy} X^k` (`Compat`). Input to [Hai14, Lemma 5.16].
-/
