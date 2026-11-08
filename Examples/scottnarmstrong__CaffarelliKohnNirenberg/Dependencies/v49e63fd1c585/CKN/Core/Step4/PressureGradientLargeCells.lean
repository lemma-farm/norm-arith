-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Morrey.Basic
set_option autoImplicit false
set_option warningAsError true
/-! # Large-cell normalization for pressure gradients

For the Morrey quantities in `prop:bootstrap`, a cell of radius `r ≥ r₀ > 0`
has normalization at most `r₀ ^ (-(5 * (1 - p / q) / p))` when `0 < p ≤ q`.
Its power integral is bounded by the whole-carrier integral. For `p = 6/5`,
the resulting factor is `r₀ ^ (5 / q - 25 / 6)` and the integral has power
`5/6`. The constant is one; the carrier radius enters only through its domain.

The indicator versions hold for every cell centre, including cells crossing
the carrier boundary. Both the origin past cylinder and the symmetric
parabolic metric ball are treated without any small-cell estimate.
-/
open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
