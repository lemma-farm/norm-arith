module
public import Mathlib.Algebra.MvPolynomial.PDeriv
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
noncomputable def W : Poly := MvPolynomial.X 1
end ComplexHermite
end GinibrePoincare
