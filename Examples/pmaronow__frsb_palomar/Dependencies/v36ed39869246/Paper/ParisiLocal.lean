module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.ParisiMild
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.PDEFixedPoint
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! # A concrete local bounded-gradient solution

The gradient Duhamel map acts on bounded continuous functions on a time
slab. Clamping time extends such functions to the full plane without
increasing their norm. The normalized Gaussian correction handles jumps
of the measure's distribution function and the terminal time.
-/
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace Paper
end Paper
