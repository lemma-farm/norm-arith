module
public import Examples.pmaronow__ccv_palomar.Dependencies.v185e775c9632.RoughRegime.MatrixKernel
public import Examples.pmaronow__ccv_palomar.Dependencies.v185e775c9632.RoughRegime.CombinedPolynomial
@[expose] public section
/-! Operator norm and convergence bridge for the full matrix/determinant
combined-index reciprocal truncation of Lemma 5(a). -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds
open RoughRegime.Upper RoughRegime.CombinedPolynomial
end RoughRegime.CombinedAnalytic
