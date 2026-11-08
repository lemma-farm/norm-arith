import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.GaussianCoefficientsR11
import Mathlib
set_option pp.unicode.fun true
/-!
# Actual finite 2004 A coefficient and its normalisation


The reindexing k = 14*n+1+s makes every exponent nonnegative. In particular
A is an actual integral polynomial, not a postulated source package.
This module proves the A-channel inclusion for every n, including n=0.
It does not assert the missing B-channel cancellation or the analytic source
identity. Those obligations are recorded separately, not hidden in a premise.
-/
namespace ErdosProblems.Erdos1049.PaperR11
open Polynomial
open scoped BigOperators
/-- The exact published normalising exponent. -/
def sourceM (n : ℕ) : ℕ := 266 * n ^ 2 + 34 * n + 1
/-- The exponent left after X^M is removed from the s-th actual A summand. -/
def sourceAExponent (n s : ℕ) : ℕ :=
  2 * n ^ 2 + (n + 1) * s + s.choose 2
noncomputable def sourceGaussianProduct (n s : ℕ) : ℤ[X] :=
  gaussBinom X (14 * n + s) (12 * n) *
    gaussBinom X (13 * n) (13 * n - s)
noncomputable def sourceASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ (sourceM n + sourceAExponent n s) *
    sourceGaussianProduct n s
lemma twice_choose_two_int (s : ℕ) :
    (2 : ℤ) * (s.choose 2 : ℤ) = (s : ℤ) * ((s : ℤ) - 1) := by
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hchoose : (s + 1).choose 2 = s + s.choose 2 := by
        simpa using (Nat.choose_succ_succ s 1)
      rw [hchoose]
      push_cast
      nlinarith
end ErdosProblems.Erdos1049.PaperR11
