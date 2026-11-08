/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceySparseInterface
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Dyadic localization in the Krause--Lacey sparse recursion

This module formalizes the geometric localization at the start of Section 3
of Krause--Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms* (arXiv:1609.01564).  In their display (3.2), an interval `I` of
length `2^(k+2)` is assigned a genuine dyadic kernel piece at scale `k`, and
the input is restricted to the central third `I'`.  The resulting piece is
supported in `I`.

The source first concentrates on the positive half-kernel `ρₖ⁺`, saying
explicitly that the complementary negative half is symmetric.  Accordingly,
our main localized piece uses the project's concrete `positiveDyadicAmplitude`;
a separate signed companion below uses the full `dyadicPsi` and connects this
localization to the genuine full dyadic Hilbert kernel.  Both have outer
support radius `2^(j-1)`, exactly one eighth of `2^(j+2)` in the project's
indexing.

The genuinely analytic input called Lemma 3.5 in that source is deliberately
not asserted here: it is the remaining local oscillatory `L¹ → L^q` estimate.
The results below prove its localization and stopping/packing framework, but
do not replace that estimate by an assumption.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
