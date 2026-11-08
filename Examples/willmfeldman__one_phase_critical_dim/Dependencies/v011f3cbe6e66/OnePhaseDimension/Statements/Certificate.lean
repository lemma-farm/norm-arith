/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
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
/-- Two-tensors on `ℝ⁵`. -/
abbrev Ten2 := Fin 5 → Fin 5 → ℝ
abbrev Ten4 := Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ
/-- The Kronecker delta. -/
def kron (i j : Fin 5) : ℝ := if i = j then 1 else 0
def sq1 (p : Ten1) : ℝ := ∑ i, p i ^ 2
/-- Squared norm of a two-tensor, `|A|² = ∑ᵢⱼ A_{ij}²`. -/
def sq2 (A : Ten2) : ℝ := ∑ i, ∑ j, A i j ^ 2
structure Coeffs where
  /-- The scalar coefficient `f`. -/
  f : Ten2 × Ten1 × ℝ → ℝ
  /-- The two-tensor coefficient `U_{jk}`. -/
  U : Ten2 × Ten1 × ℝ → Ten2
  /-- The four-tensor coefficient `K_{lijk}`. -/
  K : Ten2 × Ten1 × ℝ → Ten4
  /-- The vector coefficient `M_l`. -/
  M : Ten2 × Ten1 × ℝ → Ten1
  /-- The vector coefficient `P_l`. -/
  P : Ten2 × Ten1 × ℝ → Ten1
namespace Coeffs
variable (c : Coeffs)
/-- `C_{lijk} = K_{lijk} − K_{iljk}`. -/
def C (x : Ten2 × Ten1 × ℝ) (l i j k : Fin 5) : ℝ := c.K x l i j k - c.K x i l j k
/-- `G_{lijk} = δ_{li} U_{jk} + C_{lijk}`. -/
def G (x : Ten2 × Ten1 × ℝ) (l i j k : Fin 5) : ℝ := kron l i * c.U x j k + c.C x l i j k
end Coeffs
end OnePhaseDimension
