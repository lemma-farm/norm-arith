/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v29ef93969eff.QuadraticCarleson.QuadraticFixedHeightAveragingCountable
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Fixed-scale parameter continuity and rational approximation of half-open bands

Continuity is asserted only with the spatial scale held fixed. The density
lemma includes the lower endpoint by taking closure from inside the open
band, so it never crosses a jump of the selected dyadic scale.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
end QuadraticCarleson
