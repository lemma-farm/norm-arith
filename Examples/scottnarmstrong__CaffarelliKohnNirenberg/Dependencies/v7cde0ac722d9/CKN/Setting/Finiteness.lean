-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Statements.SuitableWeakSolutionIntegrable
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.Monotonicity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.ScalingQuantities
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Topology
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
/-!
# Finiteness of the scale quantities on suitable weak solutions

The quantities `α`, `β`, `γ`, `δ`, `λ` of `paper/ckn.tex` are real-valued, so the
lemmas `lem:monotonicity` and `lem:scaling-quantities` for them carry side
conditions saying that the underlying nonnegative integrals are finite (a
necessary input when passing an `ℝ≥0∞` integral to `ℝ≥0`).  The class `def:sws`
of suitable weak solutions supplies exactly these finiteness properties on every
local box, and this file transfers them to the parabolic cylinders `Q_r(z)` of
the monotonicity and scaling statements.

The main transfer fact is that a cylinder whose closure lies in the open carrier
`Ω × I` is contained in a local box: the spatial slice is enclosed in a metric
thickening of its closed ball, and the time slice in a thickening of its closed
interval, both chosen small enough to stay inside `Ω` and `I`.
-/
/-! ### Elementary comparisons of the two norms on `Vec3` -/
end CKN
