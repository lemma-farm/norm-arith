/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import SparseStackV3.Occupation
import SparseStackV3.Base.SparseStackDistribution
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

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

/-- A constant sum over the `b` buckets. -/
theorem sum_const_fin (c : ℝ) : (∑ _h : Fin b, c) = (b : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The bucket indicator `1_{c = ·}` sums to one. -/
theorem sum_ite_left (c : Fin b) : (∑ h : Fin b, (if c = h then (1 : ℝ) else 0)) = 1 := by
  simp

/-- The bucket indicator `1_{· = d}` sums to one. -/
theorem sum_ite_right (d : Fin b) : (∑ h : Fin b, (if h = d then (1 : ℝ) else 0)) = 1 := by
  simp

/-- Composition of two bucket indicators: `Σ_𝔥 1_{c = 𝔥} 1_{𝔥 = d} = δ_{cd}`. -/
theorem sum_ite_mul_ite (c d : Fin b) :
    (∑ h : Fin b, (if c = h then (1 : ℝ) else 0) * (if h = d then (1 : ℝ) else 0))
      = if c = d then (1 : ℝ) else 0 := by
  have e : ∀ h : Fin b, (if c = h then (1 : ℝ) else 0) * (if h = d then (1 : ℝ) else 0)
      = if c = h then (if c = d then (1 : ℝ) else 0) else 0 := by
    intro h
    by_cases hch : c = h
    · subst hch; simp
    · rw [if_neg hch, if_neg hch, zero_mul]
  rw [Finset.sum_congr rfl fun h _ => e h]
  simp

/-- Orthonormality of the bucket indicators: `Σ_a 1_{c = a} 1_{d = a} = δ_{cd}`. -/
theorem sum_ite_mul_ite' (c d : Fin b) :
    (∑ a : Fin b, (if c = a then (1 : ℝ) else 0) * (if d = a then (1 : ℝ) else 0))
      = if c = d then (1 : ℝ) else 0 := by
  have e : ∀ a : Fin b, (if c = a then (1 : ℝ) else 0) * (if d = a then (1 : ℝ) else 0)
      = if c = a then (if c = d then (1 : ℝ) else 0) else 0 := by
    intro a
    by_cases hca : c = a
    · subst hca
      by_cases hcd : c = d
      · subst hcd; simp
      · simp [hcd, Ne.symm hcd]
    · rw [if_neg hca, if_neg hca, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp

/-- A sum over the two Rademacher signs. -/
theorem sum_sign (g : Sign → ℝ) : (∑ z : Sign, g z) = g Sign.plus + g Sign.minus := by
  have huniv : (Finset.univ : Finset Sign) = {Sign.plus, Sign.minus} := rfl
  rw [huniv, Finset.sum_pair (by decide)]

/-- The product of the values of two signs is `+1` when they agree and `-1` otherwise. -/
theorem sign_mul_val (z w : Sign) : z.val * w.val = if z = w then (1 : ℝ) else -1 := by
  cases z <;> cases w <;> simp [Sign.val_plus, Sign.val_minus]

/-- A sum over the `2b` points of one site, with the two signs summed first. -/
theorem sum_signedHash (f : SignedHash b → ℝ) :
    (∑ x : SignedHash b, f x)
      = ∑ h : Fin b, (f (h, Sign.plus) + f (h, Sign.minus)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun h _ => sum_sign fun z => f (h, z)

/-- A sum over the three local levels of subsection `new:local`. -/
theorem sum_level (g : Level → ℝ) :
    (∑ l : Level, g l) = g Level.vac + g Level.light + g Level.heavy := by
  have huniv : (Finset.univ : Finset Level) = {Level.vac, Level.light, Level.heavy} := rfl
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The local expectation is the average over the `2b` points of the site: for the uniform
selector law `loc b`, `E[f] = (Σ_x f(x))/(2b)`. -/
theorem expect_selector (hb : 0 < b) (f : SignedHash b → ℝ) :
    (selectorLaw b hb).expect f = (∑ x : SignedHash b, f x) / (2 * (b : ℝ)) := by
  have hw : ∀ x : SignedHash b, (selectorLaw b hb).weight x = 1 / (2 * (b : ℝ)) := by
    intro x
    norm_num [selectorLaw]
  simp only [FiniteLaw.expect, hw]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation of a finite sum of observables is the sum of the expectations. -/
theorem expect_sum {α : Type*} [Fintype α] {ι : Type*} [Fintype ι]
    (μ : FiniteLaw α) (F : ι → α → ℝ) :
    μ.expect (fun y => ∑ i, F i y) = ∑ i, μ.expect (F i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- The single computation behind every case of `expect_kern_mul`.  All the products of two
level kernels are, after the sign sum has been carried out, affine combinations of
`1_{c = 𝔥} 1_{𝔥 = d}`, `1_{c = 𝔥}`, `1_{𝔥 = d}` and `1`, whose bucket sums are
`δ_{cd}`, `1`, `1` and `b`. -/
theorem expect_selector_of_quad (hb : 0 < b) (f : SignedHash b → ℝ) (c d : Fin b)
    (A B C D val : ℝ)
    (hf : ∀ h : Fin b, f (h, Sign.plus) + f (h, Sign.minus)
      = A * ((if c = h then (1 : ℝ) else 0) * (if h = d then (1 : ℝ) else 0))
        + B * (if c = h then (1 : ℝ) else 0)
        + C * (if h = d then (1 : ℝ) else 0) + D)
    (hval : A * (if c = d then (1 : ℝ) else 0) + B + C + (b : ℝ) * D = 2 * (b : ℝ) * val) :
    (selectorLaw b hb).expect f = val := by
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [expect_selector hb, sum_signedHash, Finset.sum_congr rfl fun h _ => hf h,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_ite_mul_ite, sum_ite_left, sum_ite_right, sum_const_fin, mul_one, mul_one, hval]
  field_simp

/-! ## 2. The three local kernels -/

/-- The **vacuum kernel** `k₀ = 1`: the reproducing kernel of the orthogonal projection
onto `ℋ₀ = ℝΩ` with `Ω = 1`, of dimension `1` (subsection `new:local`). -/
def k0 : ℝ := 1

/-- The **light kernel** `k₁(x, y) = b σ(x) σ(y) 1_{𝔥(x) = 𝔥(y)}`: the reproducing kernel of
the orthogonal projection onto `ℋ₁ = span {e_a}` with `e_a = √b σ 1_{𝔥 = a}`, of dimension
`b` (subsection `new:local`).  Equivalently `k₁ = Σ_a e_a ⊗ e_a`, see `k1_eq_sum`. -/
def k1 (x y : SignedHash b) : ℝ :=
  (b : ℝ) * ((x.2).val * (y.2).val) * (if x.1 = y.1 then 1 else 0)

/-- The **heavy kernel** `k₂(x, y) = b 1_{𝔥(x) = 𝔥(y)} - 1`: the reproducing kernel of the
orthogonal projection onto `ℋ₂ = L²₀([b])`, the mean-zero functions of the local hash, of
dimension `b - 1` (subsection `new:local`). -/
def k2 (x y : SignedHash b) : ℝ :=
  (b : ℝ) * (if x.1 = y.1 then 1 else 0) - 1

/-- The reproducing kernel of the level `l ∈ {vacuum, light, heavy}` of the local space
`L²({±1} × [b])` of subsection `new:local`. -/
def kern : Level → SignedHash b → SignedHash b → ℝ
  | Level.vac => fun _ _ => k0
  | Level.light => k1
  | Level.heavy => k2

@[simp] theorem kern_vac (x y : SignedHash b) : kern Level.vac x y = k0 := rfl

@[simp] theorem kern_light (x y : SignedHash b) : kern Level.light x y = k1 x y := rfl

@[simp] theorem kern_heavy (x y : SignedHash b) : kern Level.heavy x y = k2 x y := rfl

/-- `k₁(x, x) = b`, the dimension of the light space `ℋ₁`. -/
@[simp] theorem k1_self (x : SignedHash b) : k1 x x = (b : ℝ) := by
  have hv : (x.2).val * (x.2).val = 1 := by
    cases h : x.2 <;> simp [Sign.val_plus, Sign.val_minus]
  rw [k1, if_pos rfl, hv]
  ring

/-- `k₂(x, x) = b - 1`, the dimension of the heavy space `ℋ₂ = L²₀([b])`. -/
@[simp] theorem k2_self (x : SignedHash b) : k2 x x = (b : ℝ) - 1 := by
  rw [k2, if_pos rfl]
  ring

/-! ## 3. Symmetry -/

/-- The light kernel is symmetric. -/
theorem k1_symm (x y : SignedHash b) : k1 x y = k1 y x := by
  rw [k1, k1]
  by_cases h : x.1 = y.1
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

/-- The heavy kernel is symmetric. -/
theorem k2_symm (x y : SignedHash b) : k2 x y = k2 y x := by
  rw [k2, k2]
  by_cases h : x.1 = y.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **Symmetry of the level kernels.**  Each of the three orthogonal projections of
subsection `new:local` is self-adjoint, i.e. `k_l(x, y) = k_l(y, x)`. -/
theorem kern_symm (l : Level) (x y : SignedHash b) : kern l x y = kern l y x := by
  cases l
  · rfl
  · exact k1_symm x y
  · exact k2_symm x y

/-! ## 4. The reproducing / composition identity

The six computations below are the orthogonality half of `new:simplex`: the three level
kernels are the kernels of mutually orthogonal projections of the local space. -/

/-- `E_y[k₀ k₀] = k₀`: the vacuum projection is idempotent. -/
theorem expect_k0_mul_k0 (hb : 0 < b) :
    (selectorLaw b hb).expect (fun _ : SignedHash b => k0 * k0) = k0 := by
  simp [k0]

/-- `E_y[k₀ k₁(y, z)] = 0`: the vacuum is orthogonal to the light space, because the local
sign averages to zero. -/
theorem expect_k0_mul_k1 (hb : 0 < b) (z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k0 * k1 y z) = 0 := by
  refine expect_selector_of_quad hb _ z.1 z.1 0 0 0 0 0 (fun h => ?_) (by ring)
  simp only [k0, k1, Sign.val_plus, Sign.val_minus]
  ring

/-- `E_y[k₀ k₂(y, z)] = 0`: the vacuum is orthogonal to the heavy space, because
`E_y[b 1_{𝔥(y) = 𝔥(z)}] = 1`. -/
theorem expect_k0_mul_k2 (hb : 0 < b) (z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k0 * k2 y z) = 0 := by
  refine expect_selector_of_quad hb _ z.1 z.1 0 0 (2 * (b : ℝ)) (-2) 0 (fun h => ?_) (by ring)
  simp only [k0, k2]
  ring

/-- `E_y[k₁(x, y) k₀] = 0`: the light space is orthogonal to the vacuum. -/
theorem expect_k1_mul_k0 (hb : 0 < b) (x : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k1 x y * k0) = 0 := by
  refine expect_selector_of_quad hb _ x.1 x.1 0 0 0 0 0 (fun h => ?_) (by ring)
  simp only [k0, k1, Sign.val_plus, Sign.val_minus]
  ring

/-- `E_y[k₁(x, y) k₁(y, z)] = k₁(x, z)`: the light projection is idempotent.  This is the
reproducing property `⟨e_a, e_c⟩ = δ_{ac}` of `new:simplex` in kernel form. -/
theorem expect_k1_mul_k1 (hb : 0 < b) (x z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k1 x y * k1 y z) = k1 x z := by
  refine expect_selector_of_quad hb _ x.1 z.1
    (2 * (b : ℝ) ^ 2 * ((x.2).val * (z.2).val)) 0 0 0 _ (fun h => ?_) ?_
  · simp only [k1, Sign.val_plus, Sign.val_minus]
    ring
  · simp only [k1]
    ring

/-- `E_y[k₁(x, y) k₂(y, z)] = 0`: the light and heavy spaces are orthogonal, because the
heavy kernel does not see the local sign. -/
theorem expect_k1_mul_k2 (hb : 0 < b) (x z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k1 x y * k2 y z) = 0 := by
  refine expect_selector_of_quad hb _ x.1 z.1 0 0 0 0 0 (fun h => ?_) (by ring)
  simp only [k1, k2, Sign.val_plus, Sign.val_minus]
  ring

/-- `E_y[k₂(x, y) k₀] = 0`: the heavy space is orthogonal to the vacuum. -/
theorem expect_k2_mul_k0 (hb : 0 < b) (x : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k2 x y * k0) = 0 := by
  refine expect_selector_of_quad hb _ x.1 x.1 0 (2 * (b : ℝ)) 0 (-2) 0 (fun h => ?_) (by ring)
  simp only [k0, k2]
  ring

/-- `E_y[k₂(x, y) k₁(y, z)] = 0`: the heavy and light spaces are orthogonal. -/
theorem expect_k2_mul_k1 (hb : 0 < b) (x z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k2 x y * k1 y z) = 0 := by
  refine expect_selector_of_quad hb _ x.1 z.1 0 0 0 0 0 (fun h => ?_) (by ring)
  simp only [k1, k2, Sign.val_plus, Sign.val_minus]
  ring

/-- `E_y[k₂(x, y) k₂(y, z)] = k₂(x, z)`: the heavy projection is idempotent.  This is the
frame identity `Σ_a |f_a⟩⟨f_a| = r_b I_{ℋ₂}` of `new:simplex` in kernel form. -/
theorem expect_k2_mul_k2 (hb : 0 < b) (x z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => k2 x y * k2 y z) = k2 x z := by
  refine expect_selector_of_quad hb _ x.1 z.1
    (2 * (b : ℝ) ^ 2) (-(2 * (b : ℝ))) (-(2 * (b : ℝ))) 2 _ (fun h => ?_) ?_
  · simp only [k2]
    ring
  · simp only [k2]
    ring

/-- **The reproducing / composition identity** for the local levels of subsection
`new:local`:
`E_y[k_l(x, y) k_{l'}(y, z)] = δ_{l l'} k_l(x, z)`.
Equivalently, the three kernels `k₀, k₁, k₂` are the kernels of mutually orthogonal
idempotents on `L²({±1} × [b])`, which is the orthogonality content of `new:simplex`. -/
@[simp] theorem expect_kern_mul (hb : 0 < b) (l l' : Level) (x z : SignedHash b) :
    (selectorLaw b hb).expect (fun y => kern l x y * kern l' y z)
      = if l = l' then kern l x z else 0 := by
  cases l <;> cases l'
  · rw [if_pos rfl]; exact expect_k0_mul_k0 hb
  · rw [if_neg (by decide)]; exact expect_k0_mul_k1 hb z
  · rw [if_neg (by decide)]; exact expect_k0_mul_k2 hb z
  · rw [if_neg (by decide)]; exact expect_k1_mul_k0 hb x
  · rw [if_pos rfl]; exact expect_k1_mul_k1 hb x z
  · rw [if_neg (by decide)]; exact expect_k1_mul_k2 hb x z
  · rw [if_neg (by decide)]; exact expect_k2_mul_k0 hb x
  · rw [if_neg (by decide)]; exact expect_k2_mul_k1 hb x z
  · rw [if_pos rfl]; exact expect_k2_mul_k2 hb x z

/-! ## 5. Completeness: the local resolution of the identity -/

/-- **The pointwise completeness identity** `k₀ + k₁ + k₂ = 2b δ`.  The three levels
`ℋ₀, ℋ₁, ℋ₂` of subsection `new:local`, of dimensions `1, b, b-1`, exhaust the local space
`L²({±1} × [b])`, of dimension `2b = 1 + b + (b-1)`: indeed the three kernels add up to
`1 + b σ(x)σ(y) 1_{𝔥(x)=𝔥(y)} + b 1_{𝔥(x)=𝔥(y)} - 1`, which is `2b` at `x = y`, is
`1 - b + b - 1 = 0` when the buckets agree but the signs differ, and is `1 + 0 - 1 = 0`
when the buckets differ. -/
theorem sum_kern (x y : SignedHash b) :
    (∑ l : Level, kern l x y) = 2 * (b : ℝ) * (if x = y then 1 else 0) := by
  rw [sum_level]
  simp only [kern_vac, kern_light, kern_heavy, k0, k1, k2, sign_mul_val]
  by_cases hh : x.1 = y.1
  · rw [if_pos hh]
    by_cases hs : x.2 = y.2
    · have hxy : x = y := by
        cases x; cases y
        simp_all
      rw [if_pos hs, if_pos hxy]
      ring
    · rw [if_neg hs, if_neg fun h : x = y => hs (congrArg Prod.snd h)]
      ring
  · rw [if_neg hh, if_neg fun h : x = y => hh (congrArg Prod.fst h)]
    ring

/-- **The local resolution of the identity.**  Summing the three reproducing kernels of
subsection `new:local` against an arbitrary local observable returns the observable:
`Σ_l E_y[k_l(x, y) f(y)] = f(x)`.  Together with `expect_kern_mul` this says that
`ℋ₀ ⊕ ℋ₁ ⊕ ℋ₂` is an orthogonal decomposition of the whole local space. -/
theorem expect_sum_kern (hb : 0 < b) (x : SignedHash b) (f : SignedHash b → ℝ) :
    (∑ l : Level, (selectorLaw b hb).expect (fun y => kern l x y * f y)) = f x := by
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have key : ∀ y : SignedHash b, (∑ l : Level, kern l x y * f y)
      = 2 * (b : ℝ) * (if x = y then f y else 0) := by
    intro y
    rw [← Finset.sum_mul, sum_kern]
    by_cases h : x = y <;> simp [h]
  calc (∑ l : Level, (selectorLaw b hb).expect (fun y => kern l x y * f y))
      = (selectorLaw b hb).expect (fun y => ∑ l : Level, kern l x y * f y) :=
        (expect_sum (selectorLaw b hb) (fun l y => kern l x y * f y)).symm
    _ = (selectorLaw b hb).expect (fun y => 2 * (b : ℝ) * (if x = y then f y else 0)) :=
        FiniteLaw.expect_congr _ key
    _ = f x := by
        rw [expect_selector hb, ← Finset.mul_sum, Finset.sum_ite_eq,
          if_pos (Finset.mem_univ x)]
        field_simp

/-! ## 6. Positivity of the diagonal and elementary bounds -/

/-- The diagonal of every level kernel is nonnegative (for `b ≥ 1`): it is the squared
norm of the corresponding reproducing vector, namely `1`, `b` and `b - 1` — the dimensions
of `ℋ₀, ℋ₁, ℋ₂` of subsection `new:local`. -/
theorem kern_diag_nonneg (hb : 0 < b) (l : Level) (x : SignedHash b) :
    0 ≤ kern l x x := by
  have h1 : (1 : ℝ) ≤ (b : ℝ) := by
    have h : (1 : ℕ) ≤ b := hb
    exact_mod_cast h
  cases l
  · rw [kern_vac, k0]; norm_num
  · rw [kern_light, k1_self]; linarith
  · rw [kern_heavy, k2_self]; linarith

/-- The light kernel takes only the three values `b`, `-b` and `0`. -/
theorem k1_cases (x y : SignedHash b) :
    k1 x y = (b : ℝ) ∨ k1 x y = -(b : ℝ) ∨ k1 x y = 0 := by
  rw [k1, sign_mul_val]
  by_cases hh : x.1 = y.1
  · rw [if_pos hh]
    by_cases hs : x.2 = y.2
    · exact Or.inl (by rw [if_pos hs]; ring)
    · exact Or.inr (Or.inl (by rw [if_neg hs]; ring))
  · exact Or.inr (Or.inr (by rw [if_neg hh]; ring))

/-- The heavy kernel takes only the two values `b - 1` and `-1`. -/
theorem k2_cases (x y : SignedHash b) :
    k2 x y = (b : ℝ) - 1 ∨ k2 x y = -1 := by
  rw [k2]
  by_cases hh : x.1 = y.1
  · exact Or.inl (by rw [if_pos hh]; ring)
  · exact Or.inr (by rw [if_neg hh]; ring)

/-- `k₁ ≤ b`: the light kernel never exceeds the dimension of the light space. -/
theorem k1_le (x y : SignedHash b) : k1 x y ≤ (b : ℝ) := by
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  rcases k1_cases x y with h | h | h <;> rw [h] <;> linarith

/-- `|k₁| ≤ b`, the uniform bound on the light kernel used in Sections 3 and 4. -/
theorem abs_k1_le (x y : SignedHash b) : |k1 x y| ≤ (b : ℝ) := by
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  rcases k1_cases x y with h | h | h
  · rw [h, abs_of_nonneg hb0]
  · rw [h, abs_neg, abs_of_nonneg hb0]
  · rw [h, abs_zero]; exact hb0

/-- `|k₂| ≤ b` for `b ≥ 1`, the uniform bound on the heavy kernel used in Sections 3
and 4. -/
theorem abs_k2_le (hb : 0 < b) (x y : SignedHash b) : |k2 x y| ≤ (b : ℝ) := by
  have h1 : (1 : ℝ) ≤ (b : ℝ) := by
    have h : (1 : ℕ) ≤ b := hb
    exact_mod_cast h
  rcases k2_cases x y with h | h
  · rw [h, abs_of_nonneg (by linarith)]; linarith
  · rw [h, abs_neg, abs_one]; exact h1

/-! ## 7. The light kernel as the frame sum of the light vectors -/

/-- **The light kernel is the light frame sum** of `new:simplex`:
`k₁(x, y) = Σ_a e_a(x) e_a(y)` with `e_a = √b σ 1_{𝔥 = a}`.  This identifies `k₁` as the
reproducing kernel of the orthogonal projection onto `ℋ₁ = span {e_a : a ∈ [b]}`. -/
theorem k1_eq_sum (x y : SignedHash b) :
    k1 x y = ∑ a : Fin b,
      (Real.sqrt (b : ℝ) * (x.2).val * (if x.1 = a then 1 else 0)) *
        (Real.sqrt (b : ℝ) * (y.2).val * (if y.1 = a then 1 else 0)) := by
  have hsq : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = (b : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg b)
  have key : ∀ a : Fin b,
      (Real.sqrt (b : ℝ) * (x.2).val * (if x.1 = a then (1 : ℝ) else 0)) *
          (Real.sqrt (b : ℝ) * (y.2).val * (if y.1 = a then (1 : ℝ) else 0))
        = (b : ℝ) * ((x.2).val * (y.2).val) *
            ((if x.1 = a then (1 : ℝ) else 0) * (if y.1 = a then (1 : ℝ) else 0)) := by
    intro a
    have hrw : (Real.sqrt (b : ℝ) * (x.2).val * (if x.1 = a then (1 : ℝ) else 0)) *
        (Real.sqrt (b : ℝ) * (y.2).val * (if y.1 = a then (1 : ℝ) else 0))
          = (Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ)) * ((x.2).val * (y.2).val) *
            ((if x.1 = a then (1 : ℝ) else 0) * (if y.1 = a then (1 : ℝ) else 0)) := by
      ring
    rw [hrw, hsq]
  rw [Finset.sum_congr rfl fun a _ => key a, ← Finset.mul_sum, sum_ite_mul_ite', k1]

end

end SparseStackV3.Op.Kernel
