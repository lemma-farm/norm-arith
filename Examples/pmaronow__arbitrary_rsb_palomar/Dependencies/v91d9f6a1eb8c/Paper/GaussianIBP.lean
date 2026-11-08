module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.Gaussian
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false
@[expose] public section
/-!
# Gaussian integration by parts

The standard Gaussian Stein identity is derived from the derivative of its
actual probability density and whole-line integration by parts. The bounded
version discharges weighted integrability. Boundary terms are discharged by
Mathlib's whole-line theorem for integrable products; no limiting boundary
identity is assumed.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
end Paper
