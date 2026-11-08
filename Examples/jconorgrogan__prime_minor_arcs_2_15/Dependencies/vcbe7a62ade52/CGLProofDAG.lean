import Mathlib
/-!
# Chen--Gupta--Li v2 proof-DAG certificate

This file deliberately contains no theorem asserting the zero-density estimate
of Chen--Gupta--Li.  It certifies finite deductions at the first problematic
transition in the printed proof: passage from a zero-dependent factor
`n ^ (-beta)` to a polynomial common to all zeros.

The source line cannot be justified by simply deleting the weights.  The
correct elementary repair is discrete Abel summation: a large weighted sum
forces a large prefix of the common polynomial when the weights are
nonnegative and decreasing.
-/
namespace CGLProofDAG
open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.zeta
/-! ## A source-independent discrete Abel certificate -/
/-- The ordered `k`-fold divisor function.  Its value at `m` is the number of
ordered factorizations of `m` into `k` positive factors. -/
def orderedDivisorCount (k : ℕ) : ArithmeticFunction ℕ :=
  (ζ : ArithmeticFunction ℕ) ^ k
/-- A coefficient sequence supported on the literal CGL dyadic interval
`(N,2N]`. -/
def dyadicCoefficient (N : ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2 * N) then a n else 0
  map_zero' := by simp [Finset.mem_Ioc]
noncomputable def dirichletPolynomial (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    b n * Complex.exp (Complex.I * (t * Real.log n))
end CGLProofDAG
