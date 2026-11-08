/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.Bohr
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The dyadic kernels used in the positive estimate

This file records the elementary, exact part of the dyadic decomposition of
the quadratic Hilbert kernel.  The quotient defining a dyadic piece is given
the value zero at the origin; this is not an arbitrary extension, since the
numerator vanishes on a whole neighbourhood of the origin.
-/
open Function Set
open scoped ContDiff Topology
namespace QuadraticCarleson
/- The bump supplied by `ContDiffBump` is one on the inner closed ball and is
supported in the outer open ball.  With these radii those balls are exactly
the two intervals required in the paper. -/
end QuadraticCarleson
