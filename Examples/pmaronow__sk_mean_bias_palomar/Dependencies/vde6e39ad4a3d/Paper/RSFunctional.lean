module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Gaussian
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Variational
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
@[expose] public section
/-!
# Concrete Parisi measures and replica-symmetric functional

`ParisiMeasure` is the actual type of probability measures on `[0,1]`.
The functional is parameterized by a potential `u`; this file does not claim
that an arbitrary supplied potential is the weak Parisi PDE solution.
-/
open Set MeasureTheory
namespace Paper
end Paper
