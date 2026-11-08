module
public import Examples.pmaronow__ccv_palomar.Dependencies.v185e775c9632.RoughRegime.MatrixDeterminant
@[expose] public section
/-!
# Absolute convergence and exact matrix reciprocal kernel sum

All matrices carry the genuine ℓ² operator norm.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.MatrixKernel
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
end RoughRegime.MatrixKernel
