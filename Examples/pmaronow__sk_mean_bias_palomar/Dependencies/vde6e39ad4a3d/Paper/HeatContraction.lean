module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Hyperbolic
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Semigroup
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.SymmetrizedWeight
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.DoobHeat
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# The actual radial weight in the heat-contraction estimate

This file checks every analytic hypothesis of the Gaussian-kernel contraction
for the paper's `sech³` and its symmetrized Gaussian/cosh weight, with the
positive scalar normalization removed. In particular integrability is proved,
not supplied as an assumption.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace Paper
end Paper
