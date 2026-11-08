module
public import Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.CriticalEndpoint
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
public section
/-!
# The critical exponent relation

The strict monotonicity proof does not assume digamma monotonicity. Weak
monotonicity follows from Mathlib's proved log-convexity of Gamma. The
Gamma functional equation then forces it to be strict: equality of the
derivatives at x<y would reverse their order after translation by one.
-/
open Set
open scoped Topology
namespace SphericalAging.CriticalExponent
noncomputable section
end
end SphericalAging.CriticalExponent
