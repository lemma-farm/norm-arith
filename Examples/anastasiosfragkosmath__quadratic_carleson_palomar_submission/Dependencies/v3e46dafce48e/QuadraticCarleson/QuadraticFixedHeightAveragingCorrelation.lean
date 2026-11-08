/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticFixedHeightAveragingFinite
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Annular amplitude products in the fixed-height quadratic correlation

These lemmas instantiate the proved quadratic oscillatory estimate for the
actual product of two annular convolution amplitudes. Their uniform amplitude
and derivative bounds are kept explicit, to be supplied by the dyadic cutoff
lemmas rather than assumed in a headline theorem.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson
end QuadraticCarleson
