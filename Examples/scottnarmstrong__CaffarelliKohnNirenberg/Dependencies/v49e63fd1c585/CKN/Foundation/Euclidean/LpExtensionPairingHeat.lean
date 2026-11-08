-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.HeatKernelIntegrable
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Heat.IntegralBounds
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
set_option warningAsError true
/-! # Product integrability for heat subordination

The heat subordination representation of the Newtonian kernel and of its first
spatial derivative integrates a Gaussian family over positive times.  The two
lemmas here supply the product integrability on `(0, ∞) × ℝ³` that licenses the
Fubini exchange, for data that is smooth with compact support.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
