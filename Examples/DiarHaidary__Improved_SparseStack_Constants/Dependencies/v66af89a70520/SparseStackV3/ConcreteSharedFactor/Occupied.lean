/- Copyright (c) 2026 Diar Heidary. Released under the MIT license. -/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v66af89a70520.SparseStackV3.ConcreteSharedFactor
import Mathlib
import Mathlib.Data.Fintype.EquivFin
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The normalized ordering map for occupied configurations

An element of `α` is a particle label; in the application it is `(g,a,i)`.
Configurations are finite sets of exactly `L` such labels. Every ordering is
represented by an actual bijection `Fin L ≃ C`, so the multiplicity is exactly
`L!`. Physical admissibility (no repeated `(g,i)` and no frozen heavy site)
can be imposed afterwards by a subtype of configurations.
-/
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace SparseStackV3.ConcreteSharedFactor.Occupied
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}
end
end SparseStackV3.ConcreteSharedFactor.Occupied
