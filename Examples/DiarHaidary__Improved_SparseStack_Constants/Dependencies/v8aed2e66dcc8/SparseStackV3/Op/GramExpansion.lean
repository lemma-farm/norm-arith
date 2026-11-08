/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.SparseStackDistribution
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The operator identity (new:operator) in explicit coordinates

This file formalizes equation `(new:operator)` of Section 2 of Version 3.0 of
the manuscript *SparseStack Is an Optimal Oblivious Subspace Embedding*,
written out in the concrete coordinates of the signed-bucket probability
space.

The manuscript's exact error multiplication operator is
```
  M = (1/m) Σ_{g,a} Σ_{i ≠ j} U_{ij} ⊗ J_{a,gi} J_{a,gj},     m = s·b,
```
and the displayed reason is the local collision identity
```
  Σ_a e_{a,gi} e_{a,gj} = b σ_{gi} σ_{gj} 1{h_{gi} = h_{gj}} .
```
The two structural inputs are the Parseval identity `Σ_i u_i u_iᵀ = I_d`,
which makes the diagonal terms `i = j` cancel against `-I_d` exactly, and
the normalization `m = s b`.

Here the manuscript's tensor product `ℝ^d ⊗ (⨂_{(g,i)} L²({±1} × [b]))` is
realized concretely as vector-valued functions on the finite sample space
`SparseFock.SparseStackDistribution.RawSample s b n`, so no abstract tensor
products appear.  The central object is the *collision variable*
`collision z g i j = σ_{g,i} σ_{g,j} 1{h_{g,i} = h_{g,j}}`, which is exactly
`(1/b) Σ_a e_{a,gi} e_{a,gj}`.

## Main results

* `collision_self` and `collision_symm`: the elementary properties
  `collision z g i i = 1` and the symmetry in `i, j`.
* `sketchGram_apply`: `(ΠᵀΠ)_{ij} = (1/s) Σ_g collision z g i j`.
* `gramError_apply`: the off-diagonal form of `(new:operator)`, i.e.
  `E = UᵀΠᵀΠU - I_d` is the hollow double sum over ordered pairs `i ≠ j`.
* `collision_eq_k1`: the bridge to the local Fock kernel
  `k₁ = b σ σ' 1{h = h'}`, written out inline so that this file does not
  depend on the sibling `Kernel` module.
* `gramError_apply_kernel`: the same identity with the manuscript's `1/m`
  normalization, `m = s b`.
-/
open scoped BigOperators InnerProductSpace
namespace SparseStackV3.Op.GramExpansion
open SparseFock
open SparseFock.SparseStackDistribution
noncomputable section
variable {s b n d : ℕ}
end
end SparseStackV3.Op.GramExpansion
