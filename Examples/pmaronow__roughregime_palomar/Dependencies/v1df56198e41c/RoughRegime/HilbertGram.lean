module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionGram
@[expose] public section
/-! Actual Hilbert-space projections expressed by the finite Gram normal equations. -/
noncomputable section
open scoped BigOperators
open RealInnerProductSpace Matrix
namespace RoughRegime.HilbertGram
open RoughRegime.ProjectionGram
variable {E n a : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]
def basisSpan (z : n → E) : Submodule ℝ E := Submodule.span ℝ (Set.range z)
instance basisSpan_finiteDimensional (z : n → E) : FiniteDimensional ℝ (basisSpan z) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range z)
end RoughRegime.HilbertGram
