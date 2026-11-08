module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.MultivariateComplexHermite
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.PairwiseRadius
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.CenterOfMassEigenfunctions
@[expose] public section
/-!
# Concrete Hermite–Laguerre polynomials (Theorem 1.4 infrastructure)

The family below uses the paper's normalized complex Hermite polynomials
and classical generalized Laguerre polynomials. The full concrete generator
identity is proved in `PolynomialEigenfunctionGenerator.lean` and equilibrium
orthogonality in `PolynomialEquilibriumOrthogonality.lean`. The algebraic basis
and unique finite expansions are proved in `PolynomialEigenfunctionBasis.lean`.
-/
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
structure PolynomialEigenfunctionData (n : ℕ) where
  a : ℕ
  b : ℕ
  m : ℕ
end
end GinibrePoincare
