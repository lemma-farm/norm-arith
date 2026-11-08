module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionGram
@[expose] public section
/-! Hermitian spectral compression and the genuine real-to-complex Gram bridge. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace RoughRegime.ComplexGram
variable {n a : Type*} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]
end RoughRegime.ComplexGram
