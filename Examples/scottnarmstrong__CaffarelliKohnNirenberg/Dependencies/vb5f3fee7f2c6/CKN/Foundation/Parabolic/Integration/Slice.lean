-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Integration.Average
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option warningAsError true
/-!
# Spatial and space-time averages

This file gives named wrappers for the two averages used on parabolic cylinders.
The definitions remain the ordinary Mathlib set averages, so existing `average`,
`eLpNorm`, and restriction lemmas apply without a second normalization convention.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
noncomputable section
namespace CKN.Foundation.Parabolic.Integration
end CKN.Foundation.Parabolic.Integration
