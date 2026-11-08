import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.FrameBasics
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorLocal
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Classification of the unperturbed zeros

The only spectral fact used is the explicit three-entry diagonal calculation
in TensorZeroAlgebra. The remaining argument is finite-dimensional linear
algebra and case analysis on the four first coordinates.
-/
noncomputable section
namespace SoberonConvexBody.Tensors
open Set
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 0
end SoberonConvexBody.Tensors
