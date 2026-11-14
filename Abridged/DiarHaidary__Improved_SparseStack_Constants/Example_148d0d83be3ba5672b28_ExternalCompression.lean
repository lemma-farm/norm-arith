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

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.ParsevalFrame ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/ParsevalFrame.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SparseFock
namespace ParsevalFrame
open scoped BigOperators InnerProductSpace
noncomputable section
/-- The real Euclidean space used for the rows of the input matrix. -/
abbrev EVec (d : ℕ) := EuclideanSpace ℝ (Fin d)
/-- Squared Euclidean norm, kept as an inner product so all finite sums remain exact. -/
def normSq {d : ℕ} (x : EVec d) : ℝ := ⟪x, x⟫_ℝ
axiom normSq_eq_norm_sq {d : ℕ} (x : EVec d) : normSq x = ‖x‖ ^ 2
/-- The rank-one matrix `x yᵀ`. -/
def outer {d : ℕ} (x y : EVec d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b ↦ x a * y b
structure Frame (n d : ℕ) where
  u : Fin n → EVec d
  parseval : (∑ i, outer (u i) (u i)) = (1 : Matrix (Fin d) (Fin d) ℝ)

def analyze {n d : ℕ} (F : Frame n d) (x : EVec d) (i : Fin n) : ℝ :=
  ⟪F.u i, x⟫_ℝ

/-- Parseval's exact energy identity. -/
axiom analysis_energy_eq {n d : ℕ} (F : Frame n d) (x : EVec d) :
    (∑ i, (analyze F x i) ^ 2) = normSq x
end
end ParsevalFrame
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.SparseStackModel ====
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
open ParsevalFrame
noncomputable section
/-- A Rademacher sign, with no zero constructor. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq

end
end SparseStackModel
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.FiniteProbability ====
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

axiom expect_congr (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, f x = g x) : μ.expect f = μ.expect g

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

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.SparseStackDistribution ====
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

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Op.Space ====
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
open SparseFock.ParsevalFrame
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
end SparseStackV3.Op

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Examples.Example_148d0d83be3ba5672b28_ExternalCompression ====
/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Exact external compression on the signed-bucket state space

The analysis map of the actual Parseval frame is an isometry at every sample.
Its adjoint is a contraction. These maps act only on the external coordinate
and commute with every physical occupation projection. The resulting norm
transfer is the external-compression step of the coordinate-frame estimates.
-/
open scoped BigOperators InnerProductSpace
namespace SparseStackV3.Op.ExternalCompression
open SparseFock ParsevalFrame SparseStackDistribution 
variable {n d s b : ℕ}
noncomputable section
def lift (F : Frame n d) (X : Vec d s b n) : Vec n s b n :=
  fun z i => ∑ a, F.u i a * X z a
axiom lift_eq_analyze (F : Frame n d) (X : Vec d s b n)
    (z : RawSample s b n) (i : Fin n) :
    lift F X z i = analyze F (WithLp.toLp 2 (X z)) i
theorem nrm2_lift (hb : 0 < b) (F : Frame n d) (X : Vec d s b n) :
    nrm2 hb (lift F X) = nrm2 hb X := by
  apply FiniteLaw.expect_congr
  intro z
  have h := analysis_energy_eq F (WithLp.toLp 2 (X z))
  rw [normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq] at h
  simpa [← lift_eq_analyze, pow_two] using h
end
end SparseStackV3.Op.ExternalCompression
