import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

-- ==== Examples.ehrlich_b__sequential_products_lean.Examples.Example_05265d9a69c5fa289d1c_SpinFactor ====
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
/-!
# Spin Factor V₃: the algebraic sequential-product core

The **spin factor** V₃ = ℝ × ℝ² is the simplest non-commutative Euclidean Jordan algebra,
isomorphic to M₂(ℝ)^sa (self-adjoint 2×2 real matrices). It provides a concrete
non-commutative instance of `SequentialProductCore` (S1 and
S3--S7).  The first-variable continuity axiom S2 is deliberately not claimed by
this module until continuity of the explicit piecewise `sqrtPSD` formula is
proved at its degenerate locus.

## Representation

An element `(a₀, a₁, a₂) : ℝ × ℝ × ℝ` corresponds to the self-adjoint matrix:

  ⎡ a₀ + a₂   a₁ ⎤
  ⎣   a₁    a₀ - a₂⎦

- `a₀` is the "trace part" (half-trace)
- `(a₁, a₂)` is the "Bloch vector"

## Structure

- **Unit**: `(1, 0, 0)` (the identity matrix)
- **Order**: `a ≥ 0` iff `a₀ ≥ 0` and `a₀² ≥ a₁² + a₂²` (positive semidefinite cone)
- **Jordan product**: `(a₀,a₁,a₂) ∘ (b₀,b₁,b₂) = (a₀b₀ + a₁b₁ + a₂b₂, a₀b₁ + b₀a₁, a₀b₂ + b₀a₂)`
- **Sequential product** (Lüders): `a & b = √a · b · √a` (matrix square root product)

## Non-commutativity

We exhibit explicit effects `a`, `b` with `a & b ≠ b & a`, proving V₃ is genuinely
non-commutative. Specifically, the projections `p = (1/2, 1/2, 0)` and
`q = (1/2, 0, 1/2)` do not commute.

## References

* Alfsen-Shultz, *Geometry of State Spaces of Operator Algebras*
* van de Wetering, arXiv:1803.11139, §5
-/
noncomputable section

/-- The spin factor V₃, represented as triples `(a₀, a₁, a₂) : ℝ × ℝ × ℝ`. -/
abbrev SpinFactor := ℝ × ℝ × ℝ
namespace SpinFactor
/-- The squared norm of the Bloch vector: `a₁² + a₂²`. -/
def blochNormSq (a : SpinFactor) : ℝ := a.2.1 ^ 2 + a.2.2 ^ 2
/-- An element is positive semidefinite if `a₀ ≥ 0` and `a₀² ≥ a₁² + a₂²`. -/
def IsNonneg (a : SpinFactor) : Prop := 0 ≤ a.1 ∧ a.blochNormSq ≤ a.1 ^ 2

/-! ### Partial Order

We define `a ≤ b` iff `b - a` is in the positive semidefinite cone. -/

/-! ### The Jordan Product

The Jordan product on V₃ is:
  `(a₀,a₁,a₂) ∘ (b₀,b₁,b₂) = (a₀b₀ + a₁b₁ + a₂b₂, a₀b₁ + b₀a₁, a₀b₂ + b₀a₂)`
-/

/-! ### Matrix Square Root

For a PSD element `a = (a₀, a₁, a₂)` with eigenvalues `λ± = a₀ ± r` where
`r = √(a₁² + a₂²)`, the square root has eigenvalues `√λ±` and the same eigenvectors.

Explicitly: `√a = (s₀, s₁, s₂)` where
  `s₀ = (√λ₊ + √λ₋) / 2`
  and `(s₁, s₂) = ((√λ₊ - √λ₋) / (2r)) · (a₁, a₂)` when `r > 0`
  or `(0, 0)` when `r = 0`.
-/
/-- The Bloch norm `r = √(a₁² + a₂²)`. -/
def blochNorm (a : SpinFactor) : ℝ := Real.sqrt a.blochNormSq
/-- The matrix square root of a PSD element of V₃. -/
def sqrtPSD (a : SpinFactor) : SpinFactor :=
  let r := blochNorm a
  let sqPlus := Real.sqrt (a.1 + r)
  let sqMinus := Real.sqrt (a.1 - r)
  let s₀ := (sqPlus + sqMinus) / 2
  if r = 0 then
    (s₀, 0, 0)
  else
    let scale := (sqPlus - sqMinus) / (2 * r)
    (s₀, scale * a.2.1, scale * a.2.2)
/-! ### The Sequential Product (Lüders Product)

The sequential product is `a & b = √a · b · √a`, computed via the 2×2 matrix
representation. An element `(a₀, a₁, a₂)` represents the symmetric matrix
`[[a₀ + a₂, a₁], [a₁, a₀ - a₂]]`. The triple product `SBS` of symmetric
matrices is symmetric, so the result lives in V₃.
-/
/-- Triple matrix product `S · B · S` in spin factor coordinates.
Given `S = [[s₀+s₂, s₁], [s₁, s₀-s₂]]` and `B = [[b₀+b₂, b₁], [b₁, b₀-b₂]]`,
computes `SBS` and reads off spin factor components. -/
def matTripleProd (s b : SpinFactor) : SpinFactor :=
  let s₀ := s.1; let s₁ := s.2.1; let s₂ := s.2.2
  let b₀ := b.1; let b₁ := b.2.1; let b₂ := b.2.2
  let sb11 := (s₀ + s₂) * (b₀ + b₂) + s₁ * b₁
  let sb12 := (s₀ + s₂) * b₁ + s₁ * (b₀ - b₂)
  let sb21 := s₁ * (b₀ + b₂) + (s₀ - s₂) * b₁
  let sb22 := s₁ * b₁ + (s₀ - s₂) * (b₀ - b₂)
  let m11 := sb11 * (s₀ + s₂) + sb12 * s₁
  let m12 := sb11 * s₁ + sb12 * (s₀ - s₂)
  let m22 := sb21 * s₁ + sb22 * (s₀ - s₂)
  ((m11 + m22) / 2, m12, (m11 - m22) / 2)

/-! ### Non-commutativity

We exhibit two rank-1 projections in V₃ whose sequential product does not commute.

- `p = (1/2, 1/2, 0)` projects onto `|+⟩` (σ₁ eigenstate)
- `q = (1/2, 0, 1/2)` projects onto `|↑⟩` (σ₃ eigenstate)

For rank-1 projections, `√p = p` (eigenvalues 0 and 1), so `p & q = PQP`.

Matrix computation:
- P = [[1/2, 1/2], [1/2, 1/2]], Q = [[1, 0], [0, 0]]
- PQP = [[1/4, 1/4], [1/4, 1/4]] ↔ (1/4, 1/4, 0)
- QPQ = [[1/2, 0], [0, 0]] ↔ (1/4, 0, 1/4)
-/

/-! ### OrderUnitSpace instance -/

/-! ### Helper lemmas for the sequential product axioms -/


set_option linter.unusedVariables false in
/-- Congruence preserves PSD: if `s` and `b` are PSD, then `matTripleProd s b` is PSD. -/
theorem matTripleProd_nonneg (s b : SpinFactor) (hs : IsNonneg s) (hb : IsNonneg b) 
    (h_SpinFactor_matTripleProd_fst : ∀ (s b : SpinFactor),
      (s.matTripleProd b).1 =
        (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2) * b.1 + 2 * s.1 * s.2.1 * b.2.1 + 2 * s.1 * s.2.2 * b.2.2)
    (h_SpinFactor_matTripleProd_det : ∀ (s b : SpinFactor),
      (s.matTripleProd b).1 ^ 2 - (s.matTripleProd b).2.1 ^ 2 - (s.matTripleProd b).2.2 ^ 2 =
        (s.1 ^ 2 - s.2.1 ^ 2 - s.2.2 ^ 2) ^ 2 * (b.1 ^ 2 - b.2.1 ^ 2 - b.2.2 ^ 2))
    :
    IsNonneg (matTripleProd s b) := by
  have hs_bn : s.2.1^2 + s.2.2^2 ≤ s.1^2 := hs.2
  have hb_bn : b.2.1^2 + b.2.2^2 ≤ b.1^2 := hb.2
  constructor
  · rw [h_SpinFactor_matTripleProd_fst]
    by_cases hd : 0 ≤ s.2.1 * b.2.1 + s.2.2 * b.2.2
    · have h1 : 0 ≤ (s.1^2 + s.2.1^2 + s.2.2^2) * b.1 :=
        mul_nonneg (by nlinarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]) hb.1
      linarith [mul_nonneg hs.1 hd]
    · push_neg at hd
      have hA_nn : 0 ≤ (s.1^2 + s.2.1^2 + s.2.2^2) * b.1 :=
        mul_nonneg (by nlinarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]) hb.1
      have hcs_prod : (s.2.1*b.2.1 + s.2.2*b.2.2)^2 ≤ (s.2.1^2+s.2.2^2)*b.1^2 := by
        calc (s.2.1*b.2.1 + s.2.2*b.2.2)^2
            ≤ (s.2.1^2+s.2.2^2)*(b.2.1^2+b.2.2^2) := by nlinarith [sq_nonneg (s.2.1*b.2.2 - s.2.2*b.2.1)]
          _ ≤ (s.2.1^2+s.2.2^2)*b.1^2 := by nlinarith [sq_nonneg s.2.1, sq_nonneg s.2.2]
      nlinarith [sq_nonneg (s.1^2 - (s.2.1^2+s.2.2^2)), sq_nonneg b.1,
                 sq_nonneg ((s.1^2+s.2.1^2+s.2.2^2)*b.1 + 2*s.1*(s.2.1*b.2.1+s.2.2*b.2.2))]
  · simp only [blochNormSq]
    linarith [h_SpinFactor_matTripleProd_det s b, mul_nonneg (sq_nonneg (s.1^2 - s.2.1^2 - s.2.2^2))
      (show 0 ≤ b.1^2 - b.2.1^2 - b.2.2^2 by linarith)]

/-! ### Key identities for sqrtPSD and matTripleProd commutativity -/

/-! ### SequentialProduct instance -/

end SpinFactor
