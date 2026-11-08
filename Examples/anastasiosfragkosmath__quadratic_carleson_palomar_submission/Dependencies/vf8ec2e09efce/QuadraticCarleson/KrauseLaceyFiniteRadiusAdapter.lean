/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceySparseInterface
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.QuadraticHilbertMaximalMeasurable
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite-radius test operators for the Krause--Lacey argument

The genuine maximal truncation is naturally `ENNReal`-valued until its
almost-everywhere finiteness is known.  To apply the finite sparse-maximal
lemma without any circular finiteness assumption, we first take a finite
maximum of sharp truncations.  Its value is an ordinary nonnegative real,
embedded in `ℂ`, and this module verifies the exact sublinearity required by
the sparse framework.
-/
open Function MeasureTheory Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
namespace KrauseLaceyFiniteRadiusAdapter
open QuadraticHilbertMaximalMeasurable
set_option autoImplicit false
noncomputable section
end
end KrauseLaceyFiniteRadiusAdapter
end QuadraticCarleson
