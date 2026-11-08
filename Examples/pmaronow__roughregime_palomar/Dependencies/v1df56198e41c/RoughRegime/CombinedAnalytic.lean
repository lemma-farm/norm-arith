module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.MatrixKernel
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.CombinedPolynomial
@[expose] public section
/-! Operator norm and convergence bridge for the full matrix/determinant
combined-index reciprocal truncation of Lemma 5(a). -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds
open RoughRegime.Upper RoughRegime.CombinedPolynomial
end RoughRegime.CombinedAnalytic
