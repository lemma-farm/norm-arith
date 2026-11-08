/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CalderonZygmundLevelRecombination
import Mathlib.MeasureTheory.Covering.DensityTheorem
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# A one-dimensional Calderón--Zygmund covering at height one

This module constructs, rather than assumes, a countable pairwise-disjoint
family of positive-radius closed intervals on which the average of `‖f‖` is
strictly larger than one.  The family covers `{x | 1 < ‖f x‖}` almost
everywhere and its total length is controlled by the `L¹` mass of `f`.

The construction uses the Besicovitch Vitali family and the Lebesgue
differentiation theorem.  Selection of intervals with the additional upper
average bound needed for the sharp height-two good part is deliberately left
to a subsequent stopping-time refinement.
-/
open Filter MeasureTheory Metric Set
open scoped ENNReal BigOperators Function Topology
namespace QuadraticCarleson
namespace CalderonZygmundDecomposition
open CalderonZygmundLevelRecombination
set_option autoImplicit false
noncomputable section
end
end CalderonZygmundDecomposition
end QuadraticCarleson
