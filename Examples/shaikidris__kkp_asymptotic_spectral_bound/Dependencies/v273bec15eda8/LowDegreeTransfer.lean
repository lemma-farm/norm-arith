module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.PositiveTwoLift
@[expose] public section
/-!
# Low-degree transfer from a flat Gram estimate

The spectral lift and its ordered energy are concrete. The only estimate
assumed here is the flat Gram bound, to be supplied by weighted clique removal
and the proved rank-two Gram theorem. This module does not assume a graph
spectral bound or prove the full uniform degree-penalized target.
-/
namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
end KKPAsymptotic
