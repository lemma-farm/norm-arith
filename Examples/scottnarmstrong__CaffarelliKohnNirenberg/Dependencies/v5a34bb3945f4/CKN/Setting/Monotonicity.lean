-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Alpha
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Beta
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Gamma
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Delta
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Lambda
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Integration.Scaling
set_option autoImplicit false
set_option warningAsError true
/-!
# Monotonicity of the scale quantities in the radius

This module formalizes Lemma `lem:monotonicity` of `paper/ckn.tex`.  For a fixed
centre `z` and radii `0 < r₁ ≤ r₂`, the five quantities `alpha`, `beta`, `gamma`,
`delta` and `lambda` of `paper/ckn.tex` grow at most like the powers of `r₂ / r₁`
printed in the lemma.  The paper's statement of the fourth inequality is the
squared form `δ(z,r₁)² ≤ (r₂/r₁)^{4/3} δ(z,r₂)²`; the companion Remark
`rem:kukavica-monotonicity` also records the equivalent unsquared form with the
exponent `2/3`.  The theorem `delta_sq_mono_radius` below proves the squared
form used by the iteration estimates.

Each inequality has two ingredients.  Enlarging the cylinder (or the time-slice
domain) makes the underlying nonnegative integral, respectively time-slice
essential supremum, monotone; this is supplied by the radius-monotonicity
lemmas of the parabolic integration library.  The remaining step is elementary
real algebra with `Real.rpow`, isolated below as lemmas over abstract reals so
that the `rpow` atoms stay opaque.

The definitions evaluate the underlying nonnegative integral with
`ENNReal.toReal`, which sends `⊤` to `0`.  The paper's inequalities therefore
require the relevant quantity at the larger radius to be finite: this is the
`hfin` hypothesis below, and it holds for the suitable weak solutions considered
in `paper/ckn.tex`.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace CKN
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
end CKN
