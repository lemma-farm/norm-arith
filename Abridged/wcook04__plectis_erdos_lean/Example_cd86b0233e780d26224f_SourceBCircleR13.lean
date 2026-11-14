import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib

-- ==== Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.QBinomialUnitIdentity ====
section
set_option pp.unicode.fun true
/-!
# Erdős #1049: finite q-binomial algebra for the 2004 small-p unit

Zudilin, Acta Arith. 111 (2004), displays (8)–(11).  After the published
integrality exponent `M` is removed, the second source coefficient is a
unit at `p = 0`.  The new algebra is the finite q-binomial theorem, the
vanishing range for exponents that hit `1`, and the constant term of
`(q^α; q)_n` for `α ≥ 1`.  This module Lean-checks those identities.  It
does not construct the source sums `A(p), B(p)`, does not prove
irrationality of `F(3/2)`, and is not the 2016 Hankel family.

The Gaussian binomial uses the same Pascal recurrence as
`AdelicHeightBridge.zudilinQBinomialPS`, as a ring element rather than a
power series.
-/
open scoped BigOperators
open Finset Polynomial
namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]
/-! ## q-Pochhammer and Gaussian binomials -/
def gaussBinom (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

end ErdosProblems.Erdos1049

end

-- ==== Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourcePolynomialR11 ====
section
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

end ErdosProblems.Erdos1049.PaperR11

end

-- ==== Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourceBClearingR12 ====
section
set_option pp.unicode.fun true
/-!
# Literal B coefficient and its first polynomial clearing

This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
open PaperR11
noncomputable def sourceBValue {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n : ℕ) : K :=
  ∑ s ∈ Finset.range (13 * n + 1), f (sourceASummand n s) *
    ((∑ l ∈ Finset.Icc 1 (2 * n + s), ((f X) ^ l - 1)⁻¹) +
      ∑ j ∈ Finset.Icc 1 (14 * n),
        (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((f X) ^ j - 1)⁻¹)
end ErdosProblems.Erdos1049.PaperR12

end

-- ==== Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.GaussianDegreeR12 ====
section
set_option pp.unicode.fun true
/-!
# Exact Gaussian and actual A degrees

The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators

/-- The printed K is integral; natural division here is justified below. -/
def sourceK (n : ℕ) : ℕ := (1091 * n ^ 2 + 81 * n + 2) / 2

end ErdosProblems.Erdos1049.PaperR12

end

-- ==== Examples.wcook04__plectis_erdos_lean.Examples.Example_cd86b0233e780d26224f_SourceBCircleR13 ====
set_option pp.unicode.fun true
/-!
# Uniform complex bound for literal B and the actual cancelled pair

The deliberately simple bound costs a polynomial factor 29*n^2 at radius
1+1/n, rather than a harmonic factor. Its logarithm is still O(log n).
All cancellation identities use the actual canonical U,V and the universal
Omega theorem, not an assumed polynomial inclusion.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators

noncomputable def sourceBComplex (n : ℕ) (z : ℂ) : ℂ :=
  sourceBValue (eval₂RingHom (Int.castRingHom ℂ) z) n
noncomputable def sourceACircleMajorant (n : ℕ) (R : ℝ) : ℝ :=
  ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) * R ^ sourceK n

set_option linter.unusedVariables false in
/-- Literal finite B, uniformly on the complete circle outside its poles. -/
theorem actual_B_complex_circle_le (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) 
    (h_ErdosProblems_Erdos1049_PaperR13_sourceBComplex_inner_bound : ∀ (n s : ℕ),
      s ≤ 13 * n →
        ∀ (R : ℝ) (z : ℂ),
          1 < R →
            ‖z‖ = R →
              ‖∑ j ∈ Finset.Icc 1 (2 * n + s), (z ^ j - 1)⁻¹ +
                    ∑ j ∈ Finset.Icc 1 (14 * n), z ^ (-(↑(j * (2 * n + s)) : ℤ)) * (z ^ j - 1)⁻¹‖ ≤
                (↑(29 * n) : ℝ) * (R - 1)⁻¹)
    (h_ErdosProblems_Erdos1049_PaperR12_actual_ASummand_complex_disk_le : ∀ (n s : ℕ),
      s ≤ 13 * n →
        ∀ (R : ℝ) (z : ℂ),
          1 ≤ R →
            ‖z‖ ≤ R →
              ‖Polynomial.eval₂ (Int.castRingHom ℂ) z
                    (ErdosProblems.Erdos1049.PaperR11.sourceASummand n s)‖ ≤
                2 ^ (40 * n) * R ^ ErdosProblems.Erdos1049.PaperR12.sourceK n)
    :
    ‖sourceBComplex n z‖ ≤ sourceACircleMajorant n R *
      (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
  classical
  unfold sourceBComplex sourceBValue
  simp only [coe_eval₂RingHom, eval₂_X]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ s ∈ range (13 * n + 1),
        ((2 : ℝ) ^ (40 * n) * R ^ sourceK n) *
          (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
      apply sum_le_sum
      intro s hs
      have hs' : s ≤ 13 * n := by have := mem_range.mp hs; omega
      rw [norm_mul]
      apply mul_le_mul
        (h_ErdosProblems_Erdos1049_PaperR12_actual_ASummand_complex_disk_le n s hs' R z hR.le hz.le)
        (h_ErdosProblems_Erdos1049_PaperR13_sourceBComplex_inner_bound n s hs' R z hR hz)
      · exact norm_nonneg _
      · positivity
    _ = _ := by simp [sourceACircleMajorant, mul_assoc]
end ErdosProblems.Erdos1049.PaperR13
