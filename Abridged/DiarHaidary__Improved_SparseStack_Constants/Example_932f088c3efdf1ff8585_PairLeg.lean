import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.QuadraticDiscriminant

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Occupation ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Occupation bookkeeping for the SparseStack local spaces

This file formalizes the purely combinatorial / arithmetic layer of Section 2.1
of *SparseStack Is an Optimal Oblivious Subspace Embedding*, Version 3.0
(Diar Heidary), namely the paragraph beginning

> Tensor the local spaces over `[s] × [n]` and then with `ℝ^d`; …
> For a type pattern let `L_g, H_g` count light and heavy sites in block `g`,
> and put `L = ∑_g L_g`, `H = ∑_g H_g`, `N = L + H`, `ν = L + 2H`.

together with

* the count transitions recorded just after Figure 1: the output counts of
  `L₊, X₊, Y₊, H₊` are respectively `(L+2, H)`, `(L, H+1)`, `(L, H+1)`,
  `(L-2, H+2)`, those of `X₀, Y₀` are `(L+2, H-1)`, and `L₀, H₀` preserve both
  totals — i.e. the "grade `+2` / grade `0`" classification of Figure 1(b);
* the block-even sector `new:even-space`,
  `𝒦^ev = span {patterns with every L_g even}`;
* the grade inequalities used at the end of Section 4 when the `(L, H)` operator
  norm bounds are converted into the grade bounds `new:alpha` and `new:chi`:
  `L ≤ ν`, `H + L/2 = ν/2`, `N ≤ ν`, and, for `X₀` and `Y₀`,
  `N ≤ ν - 1` (from `H ≥ 1`) and
  `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` for `ν ≥ 2`.

Nothing analytic happens here: a *type pattern* is modelled as a function from
the site set `[s] × [n]` to the three local levels `vacuum / light / heavy`, and
all statements are finite combinatorics over `ℕ` (Sections 1–4 below) or
elementary inequalities over `ℝ` (Section 5 below).

## Main results

* `SparseStackV3.Occupation.grade_eq_sum_weight` — the two descriptions of `ν`
  agree: `ν = L + 2H` equals the sum of the local weights over all sites.
* `SparseStackV3.Occupation.L_le_grade`, `two_mul_H_le_grade`, `N_le_grade` —
  the elementary grade inequalities over `ℕ`.
* `SparseStackV3.Occupation.even_grade_of_blockEven` — the block-even sector
  `new:even-space` sits inside the even grades.
* `SparseStackV3.Occupation.grade_Lplus`, …, `grade_Yzero` — the transition
  arithmetic of Figure 1(b).
* `SparseStackV3.Occupation.Real.mul_H_add_two_le`,
  `SparseStackV3.Occupation.Real.sq_div_eight_le_sq_div_four` — the chain
  `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` for `ν ≥ 2`.
-/
namespace SparseStackV3
namespace Occupation
open scoped BigOperators
/-! ## 1. Local levels, sites and type patterns -/
/-- The three local levels carried by a site `(g, i) ∈ [s] × [n]` in the
local-space decomposition of Section 2.1: the vacuum, the *light* level (one
`P`-excitation) and the *heavy* level (one `R`-excitation). -/
inductive Level : Type
  | vac : Level
  | light : Level
  | heavy : Level
  deriving DecidableEq, Repr
namespace Level
instance : Fintype Level where
  elems := {Level.vac, Level.light, Level.heavy}
  complete := by rintro (_ | _ | _) <;> decide

end Level
/-- The site set `[s] × [n]` of Section 2.1: `s` sketch blocks, each carrying
`n` columns. -/
abbrev Site (s n : ℕ) : Type := Fin s × Fin n

variable {s n : ℕ}
/-! ## 2. The occupation counts `L_g, H_g, L, H, N, ν` -/

section Transitions
variable (Lc Hc ν : ℕ)
end Transitions
/-! ## 6. The real grade inequalities used at the end of Section 4

The passage after `new:chi` reads:

> For `X₀` use `H ≥ 1`, giving `N ≤ ν - 1` and `d + L + 1 ≤ d + ν - 1`.
> For `Y₀` use `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` (`ν ≥ 2`).
> The latter inequality is equivalent to `ν² ≥ 2`.
> The other terms follow from `L ≤ ν`, `H + L/2 = ν/2`, and `N - 1 ≤ ν - 1`.

These are stated over `ℝ` because they are applied to the real operator-norm
bounds of `new:family-bounds`. -/
namespace Real
variable {L H ν : ℝ}
end Real
end Occupation
end SparseStackV3

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.SparseStackModel ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/SparseStackModel.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SparseFock
namespace SparseStackModel
open scoped BigOperators InnerProductSpace

noncomputable section
/-- A Rademacher sign, with no zero constructor. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq
/-- The exact real value of a Rademacher sign. -/
def Sign.val : Sign → ℝ
  | .plus => 1
  | .minus => -1

end
end SparseStackModel
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.FiniteProbability ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/FiniteProbability.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Elementary probability on finite types

This file supplies a small, explicit probability foundation for the finite
random objects in the sparse-Fock argument.  A `FiniteLaw α` is a nonnegative
real weight on the finite type `α` whose total mass is one.  Expectations and
event probabilities are finite sums, so none of the results below hide
measurability, integrability, or independence hypotheses.

The main construction is `FiniteLaw.independentProduct`.  Its outcome is a
function `x : ι → α`, and its mass is the literal product of the coordinate
masses.  The coordinate marginal, separated-observable factorization, and
cylinder-event factorization theorems therefore give genuine mutual
independence of the coordinates.
-/
open scoped BigOperators
namespace SparseFock
noncomputable section
/-- A probability law on a finite type, represented by explicit real weights. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  /-- Probability mass of an outcome. -/
  weight : α → ℝ
  /-- Every outcome has nonnegative mass. -/
  weight_nonneg : ∀ x, 0 ≤ weight x
  /-- The total mass is one. -/
  sum_weight : ∑ x, weight x = 1
namespace FiniteLaw
variable {α β ι κ : Type*}
section Basic
variable [Fintype α]
/-- The expectation of a real-valued observable under a finite law. -/
def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

end Basic
section IndependentProduct
variable [Fintype ι] [DecidableEq ι] [Fintype α]
universe u_alpha_ip u_iota_ip
/-- Product law with independent coordinates.  The joint mass is definitionally
the product of the individual coordinate masses. -/
def independentProduct {α : Type u_alpha_ip} {ι : Type u_iota_ip}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  weight_nonneg x := Finset.prod_nonneg fun i _hi => (μ i).weight_nonneg (x i)
  sum_weight := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).sum_weight, Finset.prod_const_one]

end IndependentProduct
end FiniteLaw
end
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.SparseStackDistribution ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/SparseStackDistribution.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SparseFock
namespace SparseStackDistribution
open SparseStackModel
noncomputable section
instance : Fintype Sign where
  elems := {.plus, .minus}
  complete x := by cases x <;> simp
@[simp] axiom card_sign : Fintype.card Sign = 2
/-- One primitive, fully independent signed-hash selector. -/
abbrev SignedHash (b : ℕ) := Fin b × Sign
/-- The primitive selector law: uniform row and independent Rademacher sign. -/
def selectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (SignedHash b) where
  weight := fun _ => 1 / (((2 : ℕ) : ℝ) * (b : ℝ))
  weight_nonneg := by
    intro _
    exact div_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg b))
  sum_weight := by
    simp [Fintype.card_prod]
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    field_simp
/-- Literal sample space for all primitive selectors. -/
abbrev RawSample (s b n : ℕ) := (Fin s × Fin n) → SignedHash b
/-- The actual product law.  Independence is supplied by the explicit product
weight, not by a proposition attached later. -/
def rawSampleLaw (s b n : ℕ) (hb : 0 < b) : FiniteLaw (RawSample s b n) :=
  FiniteLaw.independentProduct (fun _ : Fin s × Fin n => selectorLaw b hb)

end
end SparseStackDistribution
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Kernel ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
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

/-! ## 3. Symmetry -/

/-! ## 4. The reproducing / composition identity

The six computations below are the orthogonality half of `new:simplex`: the three level
kernels are the kernels of mutually orthogonal projections of the local space. -/

/-! ## 5. Completeness: the local resolution of the identity -/

/-! ## 6. Positivity of the diagonal and elementary bounds -/

/-! ## 7. The light kernel as the frame sum of the light vectors -/

end
end SparseStackV3.Op.Kernel

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Space ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The concrete state space and the exact multiplication operator

This file realizes Section 2 of the manuscript *SparseStack Is an Optimal
Oblivious Subspace Embedding* (Version 3.0), subsection `new:local`, at the
level of the ambient Hilbert space and the exact error multiplication
operator of equation `new:operator`.

The manuscript tensors the local spaces `L²({±1} × [b])` over the sites
`(g,i) ∈ [s] × [n]` and then with `ℝ^d`.  Because the tensor product of the
local `L²` spaces *is* `L²` of all the independent hash/sign variables (this
is the first sentence of the proof of Proposition `new:cutoff`), the whole
space is realized **concretely**, with no abstract tensor products, as the
space

  `Vec d s b n = RawSample s b n → (Fin d → ℝ)`

of `ℝ^d`-valued functions on the finite sample space, equipped with the
`L²(Ω ; ℝ^d)` inner product `ip` taken against the product law
`rawSampleLaw`.  Under this identification the manuscript's operator

  `𝓜 = (1/m) ∑_{g,a} ∑_{i≠j} U_{ij} ⊗ J_{a,gi} J_{a,gj}`      (`new:operator`)

"acts on vector-valued functions by multiplication by `E`", where
`E = UᵀΠᵀΠU - I_d` is the Gram error.  `M` is therefore *defined* to be that
multiplication operator, which is the content of the displayed sentence; the
local Jacobi expansion `new:Jacobi` is not needed for the statements proved
here.

The main result is `moment_identity`, the un-truncated form of
Proposition `new:cutoff` (equation `new:moment-identity`):

  `𝔼 tr E^{2q} = ∑_{a=1}^{d} ‖𝓜^q (v_a ⊗ Ω)‖²`.

The manuscript's projected operator `M_q = Q_q 𝓜 Q_q` is omitted here: the
proof of Proposition `new:cutoff` shows `M_q^j(v_a ⊗ Ω) = 𝓜^j(v_a ⊗ Ω)` for
`0 ≤ j ≤ q`, so the two sides of `new:moment-identity` agree with the
un-truncated ones, and the un-truncated identity is exactly what the
downstream majorant argument (Lemma `new:majorant`) consumes; see
`moment_le_of_nrm2_le`.
-/
open scoped BigOperators
namespace SparseStackV3.Op
open SparseFock

open SparseFock.SparseStackModel
open SparseFock.SparseStackDistribution
variable {d s b n : ℕ}
/-! ## The concrete state space -/
/-- The concrete realization of `ℝ^d ⊗ L²(Ω)`, where `Ω` is the signed-bucket
probability space of the manuscript's subsection `new:local`: since the tensor
product of the local spaces `L²({±1} × [b])` over the sites `(g,i)` is `L²` of
all the independent hash/sign variables, a state is simply an `ℝ^d`-valued
function on the sample space. -/
abbrev Vec (d s b n : ℕ) := RawSample s b n → (Fin d → ℝ)
/-- The `L²(Ω ; ℝ^d)` inner product: the expectation, under the SparseStack
product law, of the Euclidean inner product of the two values.  This is the
manuscript's inner product `⟨·,·⟩` "extended to tensor products in the usual
way". -/
noncomputable def ip (hb : 0 < b) (F G : Vec d s b n) : ℝ :=
  (rawSampleLaw s b n hb).expect (fun z => ∑ a : Fin d, F z a * G z a)
/-- The squared `L²(Ω ; ℝ^d)` norm `‖·‖²` of the manuscript. -/
noncomputable def nrm2 (hb : 0 < b) (F : Vec d s b n) : ℝ := ip hb F F

/-! ## Elementary properties of the inner product -/

/-- The squared `L²(Ω ; ℝ^d)` norm is nonnegative. -/
axiom nrm2_nonneg (hb : 0 < b) (F : Vec d s b n) : 0 ≤ nrm2 hb F
/-! ## Linearity and self-adjointness of the multiplication operator -/

end SparseStackV3.Op

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Norm ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The Euclidean norm on the state space: Cauchy-Schwarz and the triangle inequality

This file supplies, for Version 3.0 of *SparseStack Is an Optimal Oblivious
Subspace Embedding* (Diar Heidary), the metric structure that the majorant
argument of Lemma `new:majorant` uses on the state space of subsection
`new:local`.

The manuscript tensors the local spaces `L²({±1} × [b])` over the sites
`(g,i) ∈ [s] × [n]` and then with `ℝ^d`, and writes `‖·‖` for the resulting
Hilbert norm; it is this `‖·‖` that appears in Proposition `new:cutoff`,
`𝔼 tr E^{2q} = ∑_a ‖M_q^q(v_a ⊗ Ω)‖²`, in the componentwise vector
`w(z)_α = ‖P_α z‖` of the proof of Lemma `new:majorant`, and in the hypothesis
`‖P_α M_q P_β‖ ≤ G_{αβ}` of equation `new:scalar-majorant`.

As in `SparseStackV3.Op.Space` and `SparseStackV3.Op.Projection`, the tensor
product is realized concretely as `Vec d s b n = RawSample s b n → (Fin d → ℝ)`
with the `L²(Ω ; ℝ^d)` inner product `SparseStackV3.Op.ip`; the norm is
therefore simply `nrm hb F = √(nrm2 hb F)`.

Deliberately, **no** `InnerProductSpace` instance is placed on `Vec d s b n`
(the space carries no `NormedAddCommGroup` structure here), so Mathlib's
`inner_mul_le_norm_mul_norm` is unavailable and Cauchy-Schwarz is proved from
scratch: for every real `t` the expansion `nrm2_add_smul`,
`‖F + tG‖² = ‖F‖² + 2t⟨F,G⟩ + t²‖G‖²`, is nonnegative, so the quadratic
`t ↦ ‖G‖² t² + 2⟨F,G⟩ t + ‖F‖²` has nonpositive discriminant
(`discrim_le_zero`), which is `ip_sq_le`; taking square roots gives `abs_ip_le`.

## Main results

* `SparseStackV3.Op.abs_ip_le` — **Cauchy-Schwarz**, `|⟨F,G⟩| ≤ ‖F‖‖G‖`.
* `SparseStackV3.Op.nrm_add_le` — the **triangle inequality**,
  `‖F + G‖ ≤ ‖F‖ + ‖G‖`.
* `SparseStackV3.Op.nrm_sum_le` — its **finite-sum form**,
  `‖∑_i F_i‖ ≤ ∑_i ‖F_i‖`, which is the inequality the proof of
  Lemma `new:majorant` applies to the family expansion `new:families` of the
  operator `new:operator`.
* `SparseStackV3.Op.nrm_P_le` and `SparseStackV3.Op.nrm_sq_eq_sum` — the
  sector decomposition of subsection `new:local` restated for the norm:
  each `P_p` is a contraction, and `‖F‖² = ∑_p ‖P_p F‖²`.
-/
open scoped BigOperators
namespace SparseStackV3.Op
open SparseFock
open SparseFock.SparseStackDistribution
open SparseStackV3.Occupation
variable {d s b n : ℕ}

/-- **Cauchy-Schwarz, squared form**: `⟨F,G⟩² ≤ ‖F‖²‖G‖²`.  A nonnegative real
quadratic has nonpositive discriminant. -/
axiom ip_sq_le (hb : 0 < b) (F G : Vec d s b n) :
    (ip hb F G) ^ 2 ≤ nrm2 hb F * nrm2 hb G
end SparseStackV3.Op

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.SiteLeg ====
section
/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Concrete one-site operators

Local kernels are lifted to the actual independent signed-bucket probability
space. Composition and adjunction below are finite expectation identities.
-/
open scoped BigOperators
namespace SparseStackV3.Op.SiteLeg
open SparseFock SparseFock.SparseStackDistribution Occupation
variable {d s b n : ℕ}
noncomputable section
abbrev LocalKernel (b : ℕ) := SignedHash b → SignedHash b → ℝ
def identity : LocalKernel b := fun x y => ∑ l : Level, Kernel.kern l x y
def tensorKernel (A : Site s n → LocalKernel b) (z w : RawSample s b n) : ℝ :=
  ∏ t, A t (z t) (w t)
def tensorApply (hb : 0 < b) (A : Site s n → LocalKernel b)
    (X : Vec d s b n) : Vec d s b n :=
  fun z c => (rawSampleLaw s b n hb).expect (fun w => tensorKernel A z w * X w c)

end
end SparseStackV3.Op.SiteLeg

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Examples.Example_932f088c3efdf1ff8585_PairLeg ====
/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-! # Two-site local blocks, with the bucket label collected before estimating -/
open scoped BigOperators
namespace SparseStackV3.Op.PairLeg
open SparseFock SparseFock.SparseStackDistribution Occupation SiteLeg
variable {d s b n : ℕ}
noncomputable section
def factors (t1 t2 : Site s n) (A B : LocalKernel b) : Site s n → LocalKernel b :=
  fun t => if t = t1 then A else if t = t2 then B else identity
def act (hb : 0 < b) (t1 t2 : Site s n) (A B : LocalKernel b)
    (X : Vec d s b n) : Vec d s b n := tensorApply hb (factors t1 t2 A B) X

axiom level_projection_energy (hb : 0 < b) {t1 t2 : Site s n} (ht : t1 ≠ t2)
    (l1 l2 : Level) (X : Vec d s b n) :
    nrm2 hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X) =
      ip hb X (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X)
theorem level_projection_contracts (hb : 0 < b) {t1 t2 : Site s n} (ht : t1 ≠ t2)
    (l1 l2 : Level) (X : Vec d s b n) :
    nrm2 hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X) ≤ nrm2 hb X := by
  have he := level_projection_energy hb ht l1 l2 X
  have hc := ip_sq_le hb X (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X)
  have h0 := nrm2_nonneg hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X)
  have h1 := nrm2_nonneg hb X
  rw [← he] at hc
  nlinarith
end
end SparseStackV3.Op.PairLeg
