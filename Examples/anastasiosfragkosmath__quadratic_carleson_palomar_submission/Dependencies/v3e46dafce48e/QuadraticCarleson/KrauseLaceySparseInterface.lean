/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.FiniteSparseMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.Bohr
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Interface to the Krause--Lacey sparse theorem

The result cited as `KL18`, Theorem 1.1, in the endpoint paper is Ben Krause
and Michael T. Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms*, Studia Math. 242 (2018), 217--229, arXiv:1609.01564.  In the
arXiv version the main statement is Theorem 1.6: for `d ≥ 2` the maximal
truncation with phase `exp (2 π i y^d)` has sparse `(1,r)` norm
`O(1 / (r - 1))`, for `1 < r ≤ 2`.

That theorem is not present in Mathlib.  Its proof uses oscillatory `TT*`, a
three-shift dyadic localization, a Calderón--Zygmund stopping recursion,
Carleson packing, John--Nirenberg, and Rademacher--Menshov.  This file begins
the missing branch with the exact project-facing pieces that can be proved
without postulating the analytic theorem:

* identification of the source's `1/4` sparseness convention with the
  project's approved `1/4` convention;
* the exact comparison `1/(p-1) ≤ p' ≤ 2/(p-1)` on `1 < p ≤ 2`;
* the algebraic dilation which reduces every nonzero quadratic modulation to
  one of the two signs occurring in the degree-two source theorem;
* linearity and sublinearity of every fixed quadratic Hilbert truncation on
  the project's test-function space, and its finite truncation maxima.

The sparseness conventions now agree exactly; no splitting or refinement is
required.  The remaining genuine adapter gap is that the full pointwise
supremum is naturally extended-real-valued until almost-everywhere finiteness
is established, while `TestOperator` is a total complex-valued function.
Fixed truncations avoid that issue.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate ENNReal Pointwise
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
