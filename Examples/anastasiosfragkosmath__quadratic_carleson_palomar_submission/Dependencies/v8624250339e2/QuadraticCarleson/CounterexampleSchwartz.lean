/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.Counterexample
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.SchwartzOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The counterexample as a Schwartz function

The paper's finite wave-packet superposition is smooth and compactly
supported, hence belongs to Schwartz space.  Bundling it this way lets the
canonical distributional quadratic Hilbert transform act on it directly.
-/
open scoped ContDiff SchwartzMap
namespace QuadraticCarleson
end QuadraticCarleson
