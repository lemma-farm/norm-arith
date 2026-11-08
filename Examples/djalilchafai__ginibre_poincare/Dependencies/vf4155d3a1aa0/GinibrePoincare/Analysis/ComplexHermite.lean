module
public import Mathlib
public import Mathlib.Data.Complex.Basic
@[expose] public section
/-!
# Univariate complex Hermite polynomials: algebraic layer

This file defines the two-variable polynomial underlying the complex Hermite
system.  The parameter `ρ` is the variance.  Thus the polynomial is

`J p q ρ = ∑ k, (-ρ)^k k! (p choose k) (q choose k) z^(p-k) w^(q-k)`.

Substitution `w = conj z` gives the usual univariate complex Hermite
polynomial.  Keeping the two formal variables separate makes the Wirtinger
operators honest partial derivatives.
-/
namespace GinibrePoincare
open scoped BigOperators ComplexConjugate
/-- The two formal coordinates `z` and `w` (later specialized to `z` and
`conj z`). -/
abbrev ComplexHermiteIndex := Fin 2
namespace ComplexHermite
abbrev Poly := MvPolynomial ComplexHermiteIndex ℂ
/-- Formal holomorphic coordinate. -/
noncomputable def Z : Poly := MvPolynomial.X 0
/-- Formal antiholomorphic coordinate. -/
noncomputable def W : Poly := MvPolynomial.X 1
/-- The unnormalized complex Hermite polynomial of bidegree `(p,q)` and
variance `ρ`. -/
noncomputable def raw (ρ : ℝ) (p q : ℕ) : Poly :=
  ∑ k ∈ Finset.range (min p q + 1),
    MvPolynomial.C (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
      (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
      Z ^ (p - k) * W ^ (q - k)
/-- Evaluation of the formal polynomial on the complex diagonal
`(z, conj z)`. -/
noncomputable def eval (ρ : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, conj z] (raw ρ p q)
end ComplexHermite
end GinibrePoincare
