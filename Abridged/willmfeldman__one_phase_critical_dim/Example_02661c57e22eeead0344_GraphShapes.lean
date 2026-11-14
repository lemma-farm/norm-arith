module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Statements.Certificate ====
public section
/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The universal algebraic certificate

All tensors are over `ℝ⁵`, written as plain functions `Fin 5 → … → ℝ`, with explicit index sums;
squared norms are sums of squares of entries (`sq1`, `sq2`), never the sup norm of the function
space. Data: `A` a symmetric trace-free matrix with `|A|² = 1`, `X` a symmetric trace-free
three-tensor, `p, ℓ ∈ ℝ⁵`, `g, w, z ∈ ℝ` (with no sign conditions on `w, z`), and
`q_l = X_{lij} A_{ij}`. The derivation `D_l` acts on functions of `(A, p, g)` by
`D_l A_{ij} = X_{lij} - q_l A_{ij}`, `D_l p_i = w A_{li} - g z δ_{li}`, `D_l g = z p_l`.

`CertificateStatement` asserts that there are smooth coefficient maps `f, U_{jk}, K_{lijk}, M_l,
P_l` of `(A, p, g)`, orthogonally equivariant with `f` invariant, `U, K` even in `p`, `P = 0` at
`g = 0`, such that with `C_{lijk} = K_{lijk} - K_{iljk}` and `G_{lijk} = δ_{li} U_{jk} + C_{lijk}`,

  `𝓘 = z²[5 U_{jk}A_{jk} + C_{lijk}(δ_{lj}A_{ik} + δ_{lk}A_{ij}) - 4f]`
    `+ [D_l G_{lijk} + (2a-1) q_l G_{lijk}] X_{ijk} + w [D_l M_l + (2a+1) q_l M_l]`
    `+ z [D_l P_l + 2a q_l P_l] + f|ℓ|² - (D_l f + 2a q_l f) ℓ_l ≥ ε* (z² + |ℓ|²)`

whenever `g² + |p|² ≤ 1`, `f ≥ ε*` there, and on the boundary data (`g = 0`, `|p| = 1`,
`Ap = λp`, `λ < 0`, `S₀ = λA - A²`,
`V_{ijk} = p_i S₀_{jk} + p_j S₀_{ki} + p_k S₀_{ij} + p_i p_j p_k`)

  `𝓢 = -λ f + U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk} + p_l M_l ≥ δ*`.

The constants are `a = 29/50`, `ε* = 438907/12000000`, `δ* = 6984137359/31250000000`.

## Differences from the source

* The 2026-09-24 version states the certificate with explicit rational tensor polynomials (its
  Table I). We state it existentially over smooth coefficient maps with the properties above; the
  tabulated polynomials are the witness. Equivariance, evenness and `P = 0` at `g = 0` are
  required on the whole space.
* The 2026-09-24 version defines `D_l` as a formal derivation on tensor polynomials in
  `A, p, g, δ`. We use the directional derivative `fderiv` along the generator vector
  `(D_l A, D_l p, D_l g)`; on polynomial maps the two agree.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace OnePhaseDimension
/-- Vectors in `ℝ⁵`. -/
abbrev Ten1 := Fin 5 → ℝ

/-- Squared norm of a vector. -/
def sq1 (p : Ten1) : ℝ := ∑ i, p i ^ 2

namespace Coeffs


end Coeffs

end OnePhaseDimension

end
end

-- ==== Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Bounds.TensorBounds ====
public section
/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Tensor bounds for the certificate

Let `A` be a symmetric trace-free `5 × 5` matrix with `tr A² = 1`, and put `θ = 4/5`. We prove
the estimates of the lemma "tensor bounds" in the section "Bounds for scalar graphs" of the
2026-09-24 version:

* `sq1_pow_mulVec_le`: `|A^k v|² ≤ θ^k |v|²` (the operator bound `‖A‖² ≤ θ`, iterated);
* `sumSq_pow_succ_le`: `|A^{k+1}|² ≤ θ^k`;
* `trace_pow_sq_le`: `(tr A^{k+2})² ≤ θ^k`;
* `trace_cube_sq_le`: `(tr A³)² ≤ 9/20`;
* `sq1_contract_le_five_sevenths`: `|X:A|² ≤ (5/7)|X|²` for a symmetric trace-free `X`;
* `sq1_contract_pow_le`: `|X:A^{k+2}|² ≤ θ^{k+1} |X|²`;
* `mixed_pow_le`: `s^h t^b ≤ (h/(h+b))^h (b/(h+b))^b` for `s, t ≥ 0`, `s + t ≤ 1`.

The proofs diagonalize `A` by an orthogonal matrix (Mathlib's spectral theorem). The
eigenvalues `α` satisfy `∑ α = 0` and `∑ α² = 1`, hence `α_i² = (∑_{j ≠ i} α_j)² ≤ 4(1 − α_i²)`.

The cubic bound: the 2026-09-24 version maximizes `∑ α³` by Lagrange multipliers; we use instead
the inequality `∑ (α_i − M)(α_i + 1/(5M))² ≤ 0` with `M = √(4/5) ≥ α_i`, which expands to
`∑ α³ ≤ M − 1/(5M) = 3/(5M)`. The bound `5/7` follows the 2026-09-24 version: `|X:A|²` is the
pairing of `X` with the symmetric trace-free part `F` of `(X:A) ⊗ A`, and
`|F|² = |ζ|²/3 + (10/21)|Aζ|²` for `ζ = X:A`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
@[expose] public noncomputable section
namespace OnePhaseDimension.Certificate
open Matrix Finset
/-! ### Orthogonal diagonalization -/

/-! ### Eigenvalues of a unit symmetric trace-free matrix -/

/-! ### Matrix bounds -/
section MatrixBounds
variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)
include hA h0 h1

end MatrixBounds
/-! ### Cubic tensors -/
/-- Squared norm of a three-tensor, `|X|² = ∑ X_{abc}²`. -/
def sq3 (X : Fin 5 → Fin 5 → Fin 5 → ℝ) : ℝ := ∑ a, ∑ b, ∑ c, X a b c ^ 2

section FiveSevenths
variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)

end FiveSevenths
section PowContract
variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)
include hA h0 h1

end PowContract
/-! ### The mixed bound -/

end OnePhaseDimension.Certificate

end
end

-- ==== Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Bounds.Contraction ====
public section
/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Norm bounds for contractions of tensors on `ℝ⁵`

Elementary Cauchy–Schwarz and operator-norm estimates for the contractions that occur in the
scalar graphs of the certificate:

* `OpBound M κ`: `|M v|² ≤ κ |v|²` for all `v`; `opBound_pow` gives `κ = (4/5)^k` for `M = A^k`;
* `sq_dot_le`: `⟨P, R⟩² ≤ |P|² |R|²`;
* `sq1_vecX_le`, `sq2_matX_le`: contracting a cubic tensor with vectors;
* `sq2_biOp_le`, `sq3_triOp_le`: applying matrices with operator bounds to the slots of a two- or
  three-tensor (the Kronecker operator bound `‖M₁ ⊗ ⋯ ⊗ M_r‖ ≤ ∏ ‖M_s‖`, proved one slot at a
  time).
-/
@[expose] public noncomputable section
namespace OnePhaseDimension.Certificate
open Matrix Finset
/-- `M` has squared operator norm at most `κ`. -/
def OpBound (M : Matrix (Fin 5) (Fin 5) ℝ) (κ : ℝ) : Prop := ∀ v, sq1 (M *ᵥ v) ≤ κ * sq1 v
section Slots
variable {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ}

end Slots
end OnePhaseDimension.Certificate

end
end

-- ==== Examples.willmfeldman__one_phase_critical_dim.Examples.Example_02661c57e22eeead0344_GraphShapes ====
/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The connected components of scalar graphs with cubic vertices

After the edges between vectors are split off, a scalar graph retained by the closure lemma
(at most two copies of `X`, every copy with three incidences) is a product of connected
components of the following seven shapes, where a *leaf* is a copy of `p` or `ℓ`:

* `c100`: one `X`, three leaves;
* `c110`: one `X` with a self-edge and one leaf;
* `c201`, `c202`, `c203`: two copies joined by `r = 1, 2, 3` edges, the other slots at leaves;
* `c211`: two copies joined by one edge, the first with a self-edge, the second with two
  leaves;
* `c221`: two copies joined by one edge, each with a self-edge.

For each shape we compute the value of the graph key (`Comp.eval_eq`) and prove the bound
`(value)² ≤ L² ∏ |leaf|² |X|^{2·#X}` (`Comp.eval_sq_le`), with `L²` given by the product rule of
the 2026-09-24 version (section "Bounds for scalar graphs"): `θ^k` for an edge of power `k`
between distinct vertices, `5/7` or `θ^{k-1}` for a self-edge of power `k = 1` or `k ≥ 2`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
@[expose] public noncomputable section
namespace OnePhaseDimension.Certificate
open Matrix Finset
/-! ### Leaves -/
section Unfold
variable  (ι : ℕ → Fin 5) 
end Unfold

namespace Comp

end Comp
/-! ### Bounds for the component values

Each lemma bounds the nested sum produced by the edges of one component shape, for arbitrary
matrices with operator bounds and arbitrary leaf vectors. -/
section ShapeBounds
variable (X : Fin 5 → Fin 5 → Fin 5 → ℝ)

set_option linter.unusedVariables false in
theorem bound_c203 {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ} (hM₁ : OpBound M₁ κ₁)
    (hM₂ : OpBound M₂ κ₂) (hM₃ : OpBound M₃ κ₃) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) 
    (h_OnePhaseDimension_Certificate_sum3_mul_sq_le : ∀ (f g : Fin 5 → Fin 5 → Fin 5 → ℝ),
      (∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, f a b c * g a b c) ^ 2 ≤
        (∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, f a b c ^ 2) *
          ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, g a b c ^ 2)
    (h_OnePhaseDimension_Certificate_sum_comm₃_ : ∀ (H : Fin 5 → Fin 5 → Fin 5 → ℝ),
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, H a b c = ∑ c : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, H a b c)
    (h_OnePhaseDimension_Certificate_sq3_triOp_le : ∀ {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ},
      OnePhaseDimension.Certificate.OpBound M₁ κ₁ →
        OnePhaseDimension.Certificate.OpBound M₂ κ₂ →
          OnePhaseDimension.Certificate.OpBound M₃ κ₃ →
            0 ≤ κ₁ →
              0 ≤ κ₂ →
                ∀ (T : Fin 5 → Fin 5 → Fin 5 → ℝ),
                  (OnePhaseDimension.Certificate.sq3 fun (a a' a'' : Fin 5) ↦
                      ∑ b : Fin 5,
                        M₁ a b * ∑ b' : Fin 5, M₂ a' b' * ∑ b'' : Fin 5, M₃ a'' b'' * T b b' b'') ≤
                    κ₁ * κ₂ * κ₃ * OnePhaseDimension.Certificate.sq3 T)
    (h_OnePhaseDimension_Certificate_sq3_nonneg : ∀ (X : Fin 5 → Fin 5 → Fin 5 → ℝ), 0 ≤ OnePhaseDimension.Certificate.sq3 X)
    :
    (∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'')) ^ 2 ≤ κ₁ * κ₂ * κ₃ * sq3 X * sq3 X := by
  set W : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a a' a'' =>
    ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * X b b' b''
  have e : ∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'') = ∑ a, ∑ a', ∑ a'', X a a' a'' * W a a' a'' := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [W, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [h_OnePhaseDimension_Certificate_sum_comm₃_]
    exact Finset.sum_congr rfl fun a'' _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b'' _ => by ring
  rw [e]
  have hW : sq3 W ≤ κ₁ * κ₂ * κ₃ * sq3 X := h_OnePhaseDimension_Certificate_sq3_triOp_le hM₁ hM₂ hM₃ hκ₁ hκ₂ X
  calc _ ≤ sq3 X * sq3 W := h_OnePhaseDimension_Certificate_sum3_mul_sq_le X W
    _ ≤ sq3 X * (κ₁ * κ₂ * κ₃ * sq3 X) := mul_le_mul_of_nonneg_left hW (h_OnePhaseDimension_Certificate_sq3_nonneg X)
    _ = _ := by ring
end ShapeBounds
/-! ### Values and bounds of the components -/
/-- Nonnegativity of the factors in the component bounds. -/
local macro "bound_nonneg" : tactic =>
  `(tactic| first
    | positivity
    | exact sq1_nonneg _
    | exact sq3_nonneg _
    | exact_mod_cast selfFactor_nonneg _)
namespace Comp
end Comp
end OnePhaseDimension.Certificate
