/-
# Polynomial sup norms on a domain boundary

The maximum-modulus principle identifies the polynomial sup norm on the
closure of a bounded planar set with the sup norm on its frontier.  A separate
closure-invariance lemma identifies this compact-closure norm with the norm on
the original set.
This is the analytic bridge between compact closure stages in an exhaustion
and the frontier-controlled smooth-domain bounds in `GeneralSymmetrized.lean`.

The boundedness hypothesis is explicit.  Although every intended smooth
convex approximation stage is bounded, `SmoothJordanDomain` currently stores
only a compact parametrized frontier and does not expose boundedness of its
carrier as a field.

## Main declarations

* `polynomialSupNorm_closure_eq_frontier_of_isBounded` -- the general
  maximum-modulus identity;
* `polynomialSupNorm_closure_carrier_eq_frontier` -- the identity specialized
  to the closure of a bounded smooth Jordan carrier;
* `polynomialSupNorm_closure_of_isBounded` -- closure invariance on bounded
  sets;
* `polynomialSupNorm_carrier_eq_frontier` -- the direct carrier/frontier
  identity for a bounded smooth Jordan carrier.
-/
import Mathlib
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ApproximationSupNorm
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.GeneralSymmetrized
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Polynomial Set
