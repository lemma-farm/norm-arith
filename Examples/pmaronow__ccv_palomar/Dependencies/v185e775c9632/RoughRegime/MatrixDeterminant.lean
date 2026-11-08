module
public import Examples.pmaronow__ccv_palomar.Dependencies.v185e775c9632.RoughRegime.MatrixUpper
public import Examples.pmaronow__ccv_palomar.Dependencies.v185e775c9632.RoughRegime.SeriesBounds
@[expose] public section
/-!
# Determinant coefficients of the matrix reciprocal kernel

The formal determinant series is built from entry polynomials in the actual
matrix variables. Its kth coefficient has total degree at most k.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.MatrixDeterminant
open RoughRegime.Upper RoughRegime.MatrixUpper
end RoughRegime.MatrixDeterminant
