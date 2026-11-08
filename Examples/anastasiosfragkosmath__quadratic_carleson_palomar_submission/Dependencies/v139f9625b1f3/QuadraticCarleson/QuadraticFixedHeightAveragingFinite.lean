/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.QuadraticFixedHeightAveraging
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite maximal consequence of the fixed-height quadratic kernel estimate

This file connects the explicit correlation majorant proved in `QuadraticTTStar`
to finite measurable linearization and the actual integral operator. The
correlation estimate remains an explicit input in this intermediate theorem;
the concrete annular cutoff specialization is not silently assumed.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson
namespace FiniteRangeKernel
end FiniteRangeKernel
end QuadraticCarleson
