-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Integration.Scaling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Doubling
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic Morrey cells and norms

This module records the extended-real Morrey seminorm on the backward
parabolic cylinders already defined by the parabolic geometry module.  The
metric-ball version is kept alongside it; the two versions are compared by
the inclusions between cylinders and metric balls.
-/
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic.Morrey
end CKN.Foundation.Parabolic.Morrey
