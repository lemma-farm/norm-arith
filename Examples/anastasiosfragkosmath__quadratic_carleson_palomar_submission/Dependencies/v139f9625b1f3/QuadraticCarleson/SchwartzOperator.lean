/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PVFourier
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.QuadraticKernelLimit
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Quadratic Carleson operators on Schwartz functions

The singular integral in the paper is unambiguous on Schwartz functions when
defined by pairing the quadratically modulated principal-value tempered
distribution with `y ↦ f (x - y)`.  This file defines that action and proves
that it is exactly the limit of the paper's symmetric truncations.  It then
defines the full and lacunary pointwise suprema.
-/
open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology
namespace QuadraticCarleson
end QuadraticCarleson
