/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CalderonZygmundLevelAtoms
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Recombining Calderón--Zygmund magnitude-level atoms

The magnitude sets form a measurable partition.  Consequently their
restrictions sum pointwise to the original function.  On a fixed finite
interval, local integrability justifies commuting the corresponding series
with the interval integral and average, and hence recombining the level atoms
into the ordinary centered atom.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators Function Topology
namespace QuadraticCarleson
namespace CalderonZygmundLevelRecombination
open PositiveEndpointOptimization PositiveLevelIntegration
open CalderonZygmundLevelAtoms
set_option autoImplicit false
noncomputable section
end
end CalderonZygmundLevelRecombination
end QuadraticCarleson
