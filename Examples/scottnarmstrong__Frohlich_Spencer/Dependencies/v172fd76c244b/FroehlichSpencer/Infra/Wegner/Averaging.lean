/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Wegner.OneSite
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Interlacing
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Regularity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Wegner-type spectral averaging for `A + diagonal (v|_Λ)`

Wegner's estimate (Fröhlich–Spencer (1983), Lemma 2.4 via Appendix C, (C.1)–(C.4),
Fröhlich–Spencer (1983)) for an arbitrary Hermitian matrix `A` on a finite set `Λ`
plus the random diagonal potential `v|_Λ`, `v ∼ productMeasure μ`, with `μ` having a density
bounded by `ρ`: the expected number of eigenvalues in a window of length `ℓ` is at most
`ρ ℓ |Λ|`, and so the probability of an eigenvalue in a window of length `2κ` is at most
`2 κ ρ |Λ|`.
-/
@[expose] public section
open Matrix Finset MeasureTheory
open scoped ENNReal
namespace FroehlichSpencer.Infra
section Averaging
variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}
end Averaging
end FroehlichSpencer.Infra
