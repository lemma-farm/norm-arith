module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.CombinedAnalytic
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ProjectionFrame
public import Mathlib
@[expose] public section
/-! The actual projected inner-product increment and its concrete truncated Gram
approximation, with small factors derived from Hilbert parent approximation. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix RealInnerProductSpace
namespace RoughRegime.ProjectionError
open RoughRegime.ProjectionGram RoughRegime.HilbertGram RoughRegime.ProjectionFrame
open RoughRegime.CombinedAnalytic RoughRegime.MatrixUpper RoughRegime.Upper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RoughRegime.ProjectionError
