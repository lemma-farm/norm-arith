-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option warningAsError true
/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
noncomputable section
namespace CKN.Foundation.Parabolic.Integration
end CKN.Foundation.Parabolic.Integration
