/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Kernel
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Space
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The orthogonal sector projections `P_p` and the resolution of the identity

This file formalizes, for Version 3.0 of *SparseStack Is an Optimal Oblivious Subspace
Embedding* (Diar Heidary), the sentence of subsection `new:local`

> Tensor the local spaces over `[s] × [n]` and then with `ℝ^d`; write `Ω` also for the
> tensor product of the local vacua. ... The subspace with fixed totals is `𝒦_{L,H}`,
> and `𝒦_ν = ⊕_{L + 2H = ν} 𝒦_{L,H}`,

namely the *orthogonal sector decomposition* of the state space along occupation
patterns that the majorant argument of Lemma `new:majorant` rests on.

**Modelling decision** (as in `SparseStackV3.Op.Kernel` and `SparseStackV3.Op.Space`).
The manuscript's tensor product `ℝ^d ⊗ (⨂_{(g,i)} L²({±1} × [b]))` is realized with no
abstract tensor products as the space `Vec d s b n = RawSample s b n → (Fin d → ℝ)` of
`ℝ^d`-valued functions on the finite sample space, and the three local levels
`ℋ₀ ⊕ ℋ₁ ⊕ ℋ₂` of one site are handled through their reproducing kernels
`kern : Level → SignedHash b → SignedHash b → ℝ`.

Accordingly the tensor factorization over the sites is realized by the **product kernel**
of a type pattern `p : Site s n → Level`,

```
  K_p(z, w) = ∏_{t ∈ [s] × [n]} k_{p(t)}(z_t, w_t),
```

and the orthogonal projection onto the sector of `p` is the integral operator with that
kernel,

```
  (P_p F)(z) = 𝔼_w [K_p(z, w) F(w)].
```

The subspace `𝒦_{L,H}` of the manuscript is then the range of `∑_{p : L(p) = L, H(p) = H} P_p`;
this file supplies everything needed about that family, and the counting bookkeeping of
`L, H, N, ν` lives in `SparseStackV3.Occupation`.

## Main results

* `SparseStackV3.Op.Projection.expect_K_mul` — the **composition law**
  `𝔼_w [K_p(z, w) K_{p'}(w, v)] = δ_{p p'} K_p(z, v)`, i.e. `P_p P_{p'} = δ_{p p'} P_p`
  (`P_comp`): each `P_p` is idempotent and distinct sectors are mutually orthogonal.
* `SparseStackV3.Op.Projection.sum_P` — the **resolution of the identity**
  `∑_p P_p = I`: the sectors exhaust the whole space.
* `SparseStackV3.Op.Projection.ip_P_left` — each `P_p` is **self-adjoint**.
* `SparseStackV3.Op.Projection.ip_P_P_of_ne` — distinct sectors are orthogonal subspaces.
* `SparseStackV3.Op.Projection.nrm2_eq_sum_nrm2` — **Parseval** for the sector
  decomposition, `‖F‖² = ∑_p ‖P_p F‖²`, and the consequence
  `SparseStackV3.Op.Projection.nrm2_P_le`, `‖P_p F‖² ≤ ‖F‖²`, which is the
  triangle-inequality input of Lemma `new:majorant`.
-/
open scoped BigOperators
namespace SparseStackV3.Op.Projection
open SparseFock
open SparseFock.SparseStackDistribution
open SparseStackV3.Occupation
variable {d s b n : ℕ}
noncomputable section
/-! ## 1. Two finite-sum utilities -/
/-- Fubini for two finite laws: a double expectation may be taken in either order,
because `FiniteLaw.expect` is a finite sum. -/
theorem expect_expect_comm {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.expect (fun x => ν.expect (fun y => f x y))
      = ν.expect (fun y => μ.expect (fun x => f x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun x _ => by ring
end
end SparseStackV3.Op.Projection
