/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.Definitions
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite maxima of sparse operators

This file develops the sparse-family and finite-maximal ingredients of Lemma
`l:weak11sparse` in the paper.  In particular, it records measurability in the
definition of a sparse family, proves that a sparse family of nondegenerate
real intervals is countable, makes the infimum defining the sparse norm
usable, and verifies the two quantitative finite-dimensional steps in the
paper's proof: the Hölder estimate for the foliation by the linearizing index
and the logarithmic choice of exponents.
-/
open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace L0Infinity
end L0Infinity
end QuadraticCarleson
