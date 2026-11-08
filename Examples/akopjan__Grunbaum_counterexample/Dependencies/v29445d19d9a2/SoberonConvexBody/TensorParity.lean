import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorMultilinear
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Exact finite parity extraction

The five identities below are identities of polynomials before integration.
They isolate the fully mixed tensor coefficients. No orthonormality or
measure-theoretic hypothesis is needed for these algebraic identities.
-/
noncomputable section
namespace SoberonConvexBody.Tensors
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def linearCombination4 (q : Fin 4 -> E4) (a b c d : Real) : E4 :=
  a • q 0 + b • q 1 + c • q 2 + d • q 3
end SoberonConvexBody.Tensors
