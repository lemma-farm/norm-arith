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

-- ==== Examples.ehrlich_b__sequential_products_lean.Examples.Example_402b3aba75084bd088ea_SpinFactor ====
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


/-- The square root of a PSD element is PSD. -/
theorem sqrtPSD_nonneg (a : SpinFactor) (ha : IsNonneg a) :
    IsNonneg (sqrtPSD a) := by
  unfold sqrtPSD blochNorm
  set r := Real.sqrt a.blochNormSq
  have h_bns_nn : 0 ≤ a.blochNormSq := by unfold blochNormSq; positivity
  have h_r_nn : 0 ≤ r := Real.sqrt_nonneg _
  have h_a1_ge_r : r ≤ a.1 := by rw [← Real.sqrt_sq ha.1]; exact Real.sqrt_le_sqrt ha.2
  have hsqP_nn : 0 ≤ Real.sqrt (a.1 + r) := Real.sqrt_nonneg _
  have hsqM_nn : 0 ≤ Real.sqrt (a.1 - r) := Real.sqrt_nonneg _
  by_cases hr0 : r = 0
  · simp only [hr0, ite_true]
    exact ⟨by positivity, by simp [blochNormSq]⟩
  · simp only [hr0, ite_false]
    have h_r_pos : 0 < r := lt_of_le_of_ne h_r_nn (Ne.symm hr0)
    constructor
    · change 0 ≤ (Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2; linarith
    · simp only [blochNormSq]
      have key : ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1) ^ 2 +
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2) ^ 2 =
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r)) ^ 2 * a.blochNormSq := by
        unfold blochNormSq; ring
      rw [key, ← Real.sq_sqrt h_bns_nn]
      have goal_eq : ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r)) ^ 2 * r ^ 2 =
          (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) ^ 2 / 4 := by
        field_simp; ring
      rw [goal_eq, div_pow, show (2 : ℝ) ^ 2 = 4 from by norm_num]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hsqP_nn hsqM_nn]) (by norm_num : (0:ℝ) ≤ 4)

/-! ### Key identities for sqrtPSD and matTripleProd commutativity -/

/-! ### SequentialProduct instance -/

end SpinFactor
