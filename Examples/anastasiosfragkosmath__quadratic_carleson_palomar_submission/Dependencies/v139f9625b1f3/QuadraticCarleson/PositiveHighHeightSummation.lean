/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveHighHeightTail
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The high contribution summed over magnitude levels

The maximal complex tails are the paper's actual high terms. A measurable
majorant permits a level-set bound without assuming that their unrestricted
real-parameter supremum is measurable. All fixed-height bounds are supplied
by the proved quadratic theorem.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration
end PositiveHighHeightEstimate
end QuadraticCarleson
