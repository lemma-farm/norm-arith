/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Occupation
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.SparseStackDistribution
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Local reproducing kernels of the three levels of one site

This file opens the operator layer of *SparseStack Is an Optimal Oblivious Subspace
Embedding*, Version 3.0 (Diar Heidary).  It formalizes the orthogonal splitting of the
local space of subsection `new:local`,

```
  L²({±1} × [b]) = ℋ₀ ⊕ ℋ₁ ⊕ ℋ₂,
  ℋ₀ = ℝΩ,      ℋ₁ = span {e_a : a ∈ [b]},      ℋ₂ = L²₀([b]),
```
of dimensions `1, b, b-1`, where `Ω = 1`, `e_a = √b σ 1_{𝔥 = a}` and
`f_a = (b 1_{𝔥 = a} - 1)/√(b-1)`.

**Modelling decision.**  The manuscript's tensor product
`ℝ^d ⊗ (⨂_{(g,i)} L²({±1} × [b]))` is realized concretely, with no abstract tensor
products, as vector-valued functions on the sample space
`SparseFock.SparseStackDistribution.RawSample s b n`.  Accordingly *one site* is the
finite probability space `SignedHash b = Fin b × Sign` carrying the uniform law
`SparseFock.SparseStackDistribution.selectorLaw b hb` of mass `1/(2b)`, and the local
inner product is the expectation `⟨u, v⟩ = E[u v]` under that law.

Instead of choosing bases for the three levels we record the **reproducing kernel** of the
orthogonal projection onto each of them:

```
  k₀(x, y) = 1,
  k₁(x, y) = b σ(x) σ(y) [𝔥(x) = 𝔥(y)]   ( = Σ_a e_a(x) e_a(y) ),
  k₂(x, y) = b [𝔥(x) = 𝔥(y)] - 1         ( = Σ_a f_a(x) f_a(y) · (b-1)/b · r_b ).
```

Every statement below is then a finite sum over the `2b` points of one site: no tensor
products, no bases and no `InnerProductSpace` instance are involved.  The three kernels
are packaged as `kern : Level → SignedHash b → SignedHash b → ℝ` along the three local
levels `vacuum / light / heavy` of `SparseStackV3.Occupation.Level`.

## Main results

* `SparseStackV3.Op.Kernel.kern_symm` — each level kernel is symmetric.
* `SparseStackV3.Op.Kernel.expect_kern_mul` — the **reproducing / composition** identity
  `E_y[k_l(x, y) k_{l'}(y, z)] = δ_{l l'} k_l(x, z)`: the three kernels are the kernels of
  mutually orthogonal projections, which is the orthogonality half of `new:simplex`.
* `SparseStackV3.Op.Kernel.sum_kern` and `SparseStackV3.Op.Kernel.expect_sum_kern` — the
  **local resolution of the identity** `k₀ + k₁ + k₂ = 2b · δ`, i.e.
  `Σ_l E_y[k_l(x, y) f(y)] = f(x)`: the three levels exhaust the local space, whose
  dimensions `1 + b + (b-1) = 2b` add up to the dimension of `L²({±1} × [b])`.
* `SparseStackV3.Op.Kernel.k1_eq_sum` — the light kernel is the frame sum
  `k₁ = Σ_a e_a ⊗ e_a` of the light vectors `e_a = √b σ 1_{𝔥 = a}` of `new:simplex`.
* `SparseStackV3.Op.Kernel.kern_diag_nonneg`, `abs_k1_le`, `abs_k2_le` — positivity of the
  diagonal and the uniform bound `b` on the two nontrivial kernels, used in the operator
  bounds of Sections 3 and 4.
-/
namespace SparseStackV3.Op.Kernel
open SparseFock SparseFock.SparseStackModel SparseFock.SparseStackDistribution
open SparseStackV3.Occupation
open scoped BigOperators
noncomputable section
variable {b : ℕ}
/-! ## 1. A finite-sum toolkit for one site -/
end
end SparseStackV3.Op.Kernel
