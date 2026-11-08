module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.GinibreMassFiniteness
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.Vandermonde
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.NormalizedGroundState
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Funext
@[expose] public section
/-! # Algebraic alternating polynomials and the Vandermonde -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
attribute [local simp] MvPolynomial.optionEquivLeft_X_none
  MvPolynomial.optionEquivLeft_X_some MvPolynomial.optionEquivLeft_C
end
end GinibrePoincare
