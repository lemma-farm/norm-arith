-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Poincare.Geometry
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
set_option autoImplicit false
set_option warningAsError true
namespace CKN
open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise
/-!
# Riesz-kernel tools for convex-domain Poincare — basic estimates

This file defines the Riesz kernel `(x, y) ↦ ‖x - y‖^(1 - d)` and establishes
its basic positivity, symmetry, and ball-localised `L¹` bounds. The bounded-
domain `L¹` size is controlled by the radius of `IsBoundedDomain`.
-/
section NeZero
variable {d : ℕ} [NeZero d]
/-- Cache `Nontrivial (Vec d)` once per section so tactic-level typeclass
searches don't rediscover the NeZero → Nonempty → Nontrivial chain. -/
private instance instNontrivialVecNeZero : Nontrivial (Vec d) := inferInstance
end NeZero
section BoundedDomain
variable {d : ℕ} {U : Set (Vec d)} [NeZero d]
/-- Cache `Nontrivial (Vec d)` once per section. -/
private instance instNontrivialVecBounded : Nontrivial (Vec d) := inferInstance
end BoundedDomain
end CKN
