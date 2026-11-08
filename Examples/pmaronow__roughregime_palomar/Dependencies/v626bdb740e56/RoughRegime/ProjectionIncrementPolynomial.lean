module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ProjectionApproximation
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ProjectionError
public import Mathlib
@[expose] public section
/-! The actual Gram-residual approximant is a polynomial of the precise source
combined degree. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionError RoughRegime.ProjectionGram
end RoughRegime.ProjectionIncrementPolynomial
