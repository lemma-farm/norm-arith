/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Count
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Stieltjes.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The normalized eigenvalue counting measure of a Hermitian matrix

`eigenvalueMeasure hH = |ι|⁻¹ ∑_i δ_{λ_i}` for a Hermitian `H : Matrix ι ι ℂ` (eigenvalues with
multiplicity).

Its distribution function is `eigenvalueCount hH E / |ι|`; for `H = H_Λ(v)` it is
the finite-volume integrated density of states `N_Λ(E, v)/|Λ|` of Fröhlich–Spencer (1983), (1.10),
Fröhlich–Spencer (1983).

Nothing here is model specific.
-/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FroehlichSpencer.Infra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}
/-- The normalized eigenvalue counting measure `|ι|⁻¹ ∑_i δ_{λ_i}`. -/
noncomputable def eigenvalueMeasure (hH : H.IsHermitian) : Measure ℝ :=
  ((Fintype.card ι : ℝ≥0∞)⁻¹) • ∑ i, Measure.dirac (hH.eigenvalues i)
theorem eigenvalueMeasure_def (hH : H.IsHermitian) :
    eigenvalueMeasure hH = ((Fintype.card ι : ℝ≥0∞)⁻¹) • ∑ i, Measure.dirac (hH.eigenvalues i) :=
  rfl
end FroehlichSpencer.Infra
