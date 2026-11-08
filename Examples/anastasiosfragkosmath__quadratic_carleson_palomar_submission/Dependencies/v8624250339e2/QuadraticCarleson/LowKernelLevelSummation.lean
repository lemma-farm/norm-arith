/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.LowKernelBadAtomSharp
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.CalderonZygmundLevelAtoms
import Mathlib.MeasureTheory.Integral.Prod
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Summing the sharp low-kernel estimate over a magnitude level

This file applies the sharp atomwise `O(B + 1)` low-kernel estimate to an
arbitrary countable pairwise-disjoint family of centered intervals.  The
atom `L¹` masses are then summed using the exact magnitude-level result from
`CalderonZygmundLevelAtoms`.  Each output is integrated on the complement of
the atom's triple interval; this is stronger than the paper's required
complement of `5I` after restriction.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators Function
namespace QuadraticCarleson
namespace LowKernelLevelSummation
open CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration
set_option autoImplicit false
noncomputable section
end
end LowKernelLevelSummation
end QuadraticCarleson
