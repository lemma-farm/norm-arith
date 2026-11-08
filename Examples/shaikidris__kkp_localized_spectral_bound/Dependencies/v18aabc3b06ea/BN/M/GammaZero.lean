/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.CP.Closed
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.M.Schur
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Order.Basic
@[expose] public section
/-!
# The `γ = 0` perturbation

If `configγ s t ρ x = 0`, enlarge the configuration by a new vector
`y* = √ε • (x*, 1)` with `x*` strictly to the right of every `t i` and
`ε > 0`. Every new `H i` is then positive, hence the enlarged `γ` is
positive (SC19). The principal submatrix of `M` on the original indices
differs from the original `M` only by diagonal `O(ε)` Laplacian terms
coming from edges to `y*`, and therefore converges as `ε ↓ 0` (SC20).
Closedness of the CP cone upgrades SC18 on the enlargements to CP of the
original `M`, including the case `p = 0` (SC21).
-/
namespace BN
open Matrix Finset Function Filter
open scoped Matrix Topology
variable {k p : ℕ}
set_option linter.unusedSectionVars false
noncomputable section
/-! ### SC19 — vanishing `H i` when `γ = 0` -/
end
end BN
