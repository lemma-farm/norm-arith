/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.QuadraticFixedHeightAveragingNorm
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.CalderonZygmundLevelAtoms
import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Genuine high-height estimate: disjoint level-atom inputs

The paper's high part uses the strict height range `r > B_k` and the input
`b_k = ∑ I, b_{I,k}`. This file constructs that countable disjoint atom sum,
proves its L² input bound from the actual atom estimates, and invokes the
proved real-parameter fixed-height quadratic maximal theorem.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration
end PositiveHighHeightEstimate
end QuadraticCarleson
