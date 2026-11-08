-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.Maximal.StrongType
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option warningAsError true
/-!
# The order-one Euclidean Riesz potential
This file supplies the geometric part of Hedberg's proof in the native
three-dimensional model `Vec3`.  The maximal majorant is the uncentred
maximal function from `Maximal.HardyLittlewood`.
-/ 
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
