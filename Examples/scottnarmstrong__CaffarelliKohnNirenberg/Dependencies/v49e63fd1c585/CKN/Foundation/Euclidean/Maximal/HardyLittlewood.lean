-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# The Euclidean Hardy--Littlewood maximal function

This module defines the uncentred maximal function on `Vec3` and proves its
weak `(1,1)` estimate by the metric Vitali covering theorem.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
