module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.CombinedAnalytic
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.KernelExpressions
@[expose] public section
/-! Actual Gram normal equations and polynomial residual factors for nested projections. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace RoughRegime.ProjectionGram
variable {n a b : Type*} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end RoughRegime.ProjectionGram
