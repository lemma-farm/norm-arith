module
public import Mathlib
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.Count
@[expose] public section
/-!
# Dimension one, finite order, and two examples on small lattices

For squarefree `χ_A` (statements (5) and (6) in their squarefree form, the `ℤ²` examples of (7),
and statement (12)): the least physical dimension is `1` exactly in the Pisot–Salem case (or for
`A = ±1` on `ℤ¹`); with all roots on the unit circle it counts `1` for each factor `x ± 1` and `2`
for each other cyclotomic factor; on `ℤ²` the identity and the Jordan matrix `[[1, 1], [0, 1]]`
share `χ = (x − 1)²` but have least physical dimensions `1` and `2`; and the companion matrix of
`x⁴ − x³ − x² − x + 1` is a non-hyperbolic example with least physical dimension `1`.

These are corollaries of the squarefree count (`isLeast_physDims_squarefree`), of the
expanding-root and Kronecker lemmas, of the normal form, and of the disk condition of statement
(1). The forms of (5) and (6) for every `χ_A` are in `InflationDimension.FormulaA`.
-/
namespace InflationDimension
open Polynomial Filter Topology Module QuadraticMap
open scoped Kronecker Pointwise
noncomputable section
namespace DimOne
section Factors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Factors
/-! ### Statement (5), from the count -/
section DimensionOne
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end DimensionOne
/-! ### Statement (6), from the count -/
section FiniteOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end FiniteOrder
/-! ### The Salem quartic -/
section Salem
end Salem
/-! ### Statement (7): the identity and the Jordan matrix on `ℤ²` -/
section Plane
end Plane
end DimOne
/-! ### The squarefree statements and the Salem witness -/
end
end InflationDimension
