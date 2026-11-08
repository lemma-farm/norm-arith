module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionApproximation
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionError
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
