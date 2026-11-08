-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Integration.Average
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# Doubling geometry for parabolic volume

The parabolic metric has homogeneous dimension five.  The lemmas below record
the corresponding scaling of the spatial balls and parabolic cylinders, then
use the cylinder/metric-ball comparison from `Basic` to provide the doubling
instance required by metric covering arguments.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
end CKN.Foundation.Parabolic
