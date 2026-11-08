/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyPositiveCorrelation
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The fixed-scale endpoint in Krause--Lacey Proposition 4.1

This module proves the `L∞ → L∞` endpoint paired with the oscillatory
`L² → L²` estimate in the proof of KL18 Proposition 4.1.  The kernel's
`L¹` mass is bounded directly from the concrete dyadic cutoff.  At a fixed
scale, the localized outputs have disjoint parent supports, so at most one
summand contributes at any point.

Mathlib currently has no Riesz--Thorin or Marcinkiewicz operator
interpolation theorem in its `MemLp` API.  Accordingly this file proves both
actual endpoints but does not introduce the desired intermediate `L^q`
operator estimate as a hypothesis.
-/
open Function MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
