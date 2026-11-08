/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Events
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Section5
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Theorem51
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Entropy
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Cubes
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Multiscale.Measurability
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Probability of a gentle singular component

FS83 Theorem 2.2: in the bounded-density large-disorder and Gaussian high-energy regimes, the probability of membership in a gentle singular component decays as a prescribed power of the scale, uniformly in the site and finite volume. Measurability is included.
-/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FroehlichSpencer.T12
open Multiscale
/-! ### Real-variable estimates -/
end FroehlichSpencer.T12
end
