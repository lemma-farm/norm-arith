/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleGeometry
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleLevelSet
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryPacketSum
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.StationaryPacketSum
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Pointwise lower bound for the negative-endpoint counterexample

This module assembles the exact off-support operator identity, the oscillatory
left tail, the stationary right tail, and the Bohr-set harmonic main term.  The
only remaining numerical input is a single inequality saying that the two
proved errors fit inside half of the main-term lower bound.
-/
open Finset Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
