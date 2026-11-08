/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Kernel
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The local level-transfer table of the Jacobi multiplier `J_a`

This file formalizes equation `new:Jacobi` of *SparseStack Is an Optimal Oblivious
Subspace Embedding*, Version 3.0 (Diar Heidary), together with the sentence that
follows it and the transition table recorded just after Figure 1.

The manuscript writes multiplication by the local light vector
`e_a = √b σ 1_{𝔥 = a}` of subsection `new:local` as the Jacobi operator

```
  J_a = P_a + P_a^* + √h (R_a + R_a^*),        h = b - 1,          (new:Jacobi)
```

with `P_a^* = |e_a⟩⟨Ω|`, `P_a = |Ω⟩⟨e_a|`, `R_a = |f_a⟩⟨e_a|`, `R_a^* = |e_a⟩⟨f_a|`,
"Indeed it sends `Ω` to `e_a`, sends `e_c` to `δ_{ac}(Ω + √h f_a)`, and sends a heavy
vector `v` to `√h ⟨f_a, v⟩ e_a`."

**Modelling decision** (fixed in `SparseStackV3.Op.Kernel`, followed here).  No abstract
tensor products and no bases are used: one site is the finite probability space
`SignedHash b = Fin b × Sign` with the uniform law `selectorLaw b hb`, and the three
local levels `vacuum / light / heavy` are handled through their reproducing kernels
`Kernel.kern`.  The `(l', l)` matrix element of multiplication by `e_a` is therefore the
kernel-dressed expectation

```
  trans l' l a x u = E_y[ k_{l'}(x, y) · e_a(y) · k_l(y, u) ].
```

Everything below is a finite computation over the `2 b` points of one site.

## Main results

* `SparseStackV3.Op.LocalTransfer.trans_eq_zero_of_not_xor` — **"every leg changes light
  parity"**: the amplitude vanishes unless exactly one of the two levels is `light`.
  This is the vanishing half of the table after Figure 1, and is restated in the grade
  language as `trans_eq_zero_of_weight`: the amplitude vanishes unless the two level
  weights differ by exactly one.
* `SparseStackV3.Op.LocalTransfer.trans_light_vac`,
  `SparseStackV3.Op.LocalTransfer.trans_vac_light`,
  `SparseStackV3.Op.LocalTransfer.trans_heavy_light`,
  `SparseStackV3.Op.LocalTransfer.trans_light_heavy` — the four nonzero amplitudes of
  `new:Jacobi`, with their exact values: `J_a` sends `Ω` to `e_a`, sends `e_c` to
  `δ_{ac}(Ω + √h f_a)` and sends a heavy vector `v` to `√h ⟨f_a, v⟩ e_a`.  Here
  `√h f_a(x) = b 1_{𝔥(x) = a} - 1`, which is the factor that dresses the two heavy legs.
* `SparseStackV3.Op.LocalTransfer.trans_symm` — the table is symmetric, i.e. `J_a` is
  self-adjoint: `P_a` and `P_a^*` (resp. `R_a` and `R_a^*`) are mutually adjoint.
* `SparseStackV3.Op.LocalTransfer.abs_trans_le` — the crude uniform bound
  `|trans| ≤ b √b`, the local input for the operator bounds of Sections 3 and 4.
* `SparseStackV3.Op.LocalTransfer.k1_eq_sum_ev` — the light kernel is the frame sum
  `k₁ = Σ_a e_a ⊗ e_a` of `new:simplex`, restated in terms of `ev`.
-/
namespace SparseStackV3.Op.LocalTransfer
open SparseFock SparseFock.SparseStackModel SparseFock.SparseStackDistribution
open SparseStackV3.Occupation
open scoped BigOperators
noncomputable section
variable {b : ℕ}
/-! ## 1. The local light vector and the transfer amplitude -/
/-- The **local light vector** `e_a` of subsection `new:local`:
`e_a(σ, 𝔥) = √b · σ · 1_{𝔥 = a}`. -/
noncomputable def ev (a : Fin b) (y : SignedHash b) : ℝ :=
  Real.sqrt (b : ℝ) * (y.2).val * (if y.1 = a then 1 else 0)
/-- The **local transfer amplitude**: the `(l', l)` matrix element of multiplication by
the light vector `e_a`, dressed by the two reproducing kernels of `new:local`,
`trans l' l a x u = E_y[k_{l'}(x, y) · e_a(y) · k_l(y, u)]`.  Ranging over the nine pairs
of levels this is the local level-transfer table of the Jacobi operator `new:Jacobi`. -/
noncomputable def trans (hb : 0 < b) (l' l : Level) (a : Fin b)
    (x u : SignedHash b) : ℝ :=
  (selectorLaw b hb).expect (fun y => Kernel.kern l' x y * ev a y * Kernel.kern l y u)
/-! ## 2. Two elementary sign-sum tools

Every entry of the table is a sum over the `2 b` points of one site.  Summing the two
signs first leaves a sum over the `b` buckets, and the only two shapes that occur are
"odd in the sign" (which vanishes) and "even in the sign with a single bucket indicator
`1_{𝔥 = a}` coming from `e_a`" (which collapses to a single bucket). -/
end
end SparseStackV3.Op.LocalTransfer
