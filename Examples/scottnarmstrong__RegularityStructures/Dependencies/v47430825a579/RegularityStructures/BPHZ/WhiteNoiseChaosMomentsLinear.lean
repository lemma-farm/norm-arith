/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialEvenMoments
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.MalliavinClosureLaw
public import Mathlib.Algebra.MvPolynomial.Monad
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment equivalence for polynomials of a centred Gaussian vector

A linear change of variables does not raise the total degree of a polynomial
(`totalDegree_bind₁_linear_le`). Since the law of a centred Gaussian vector with covariance `C` is
the image of the standard Gaussian measure under a matrix `A` with `A * A = C`
(`centredGaussianVector_standard_representation`), the dimension-free moment equivalence
`exists_integral_eval_pow_two_mul_le_of_totalDegree_le` transfers to every centred Gaussian vector,
with the same constant.
-/
public section
open MvPolynomial MeasureTheory ProbabilityTheory
namespace RegularityStructures
universe u
variable {n : ℕ}
/-- The polynomial `∑ⱼ Aᵢⱼ Xⱼ` has total degree at most `1`. -/
private lemma totalDegree_linearForm_le (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∑ j, C (A i j) * (X j : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp
/-- Substituting polynomials of total degree at most `1` does not raise the total degree. -/
theorem totalDegree_bind₁_le_of_totalDegree_le_one {g : Fin n → MvPolynomial (Fin n) ℝ}
    (hg : ∀ i, (g i).totalDegree ≤ 1) (f : MvPolynomial (Fin n) ℝ) :
    (bind₁ g f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (g i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i * 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left _ (hg i))
    _ = s.sum fun _ e => e := by simp [Finsupp.sum]
    _ ≤ f.totalDegree := le_totalDegree hs
/-- Pulling a polynomial back along a matrix `A` does not raise its degree: there is a polynomial
`f'` with `eval y f' = eval (A y) f` and `totalDegree f' ≤ totalDegree f`. -/
theorem exists_eval_mulVec_eq_of_totalDegree_le (A : Matrix (Fin n) (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ) :
    ∃ f' : MvPolynomial (Fin n) ℝ, f'.totalDegree ≤ f.totalDegree ∧
      ∀ y, eval y f' = eval (A.mulVec y) f := by
  refine ⟨bind₁ (fun i => ∑ j, C (A i j) * (X j : MvPolynomial (Fin n) ℝ)) f,
    totalDegree_bind₁_le_of_totalDegree_le_one (fun i => totalDegree_linearForm_le A i) f,
    fun y => ?_⟩
  have h := eval₂Hom_bind₁ (RingHom.id ℝ) y
    (fun i => ∑ j, C (A i j) * (X j : MvPolynomial (Fin n) ℝ)) f
  have hy : ∀ i, eval₂Hom (RingHom.id ℝ) y
      (∑ j, C (A i j) * (X j : MvPolynomial (Fin n) ℝ)) = A.mulVec y i := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  simp only [hy] at h
  exact h
theorem integrable_eval_pow_of_isCentredGaussianVector {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (f : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    Integrable (fun ω => (eval (X ω) f) ^ k) P := by
  obtain ⟨A, -, -, hlaw⟩ := centredGaussianVector_standard_representation hX
  have hAmeas : Measurable (Matrix.mulVecLin A) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hc : Continuous fun x : Fin n → ℝ => (eval x f) ^ k := (f.continuous_eval).pow _
  have h1 : Integrable (fun x : Fin n → ℝ => (eval x f) ^ k) (P.map X) := by
    rw [hlaw, integrable_map_measure hc.aestronglyMeasurable hAmeas.aemeasurable]
    obtain ⟨f', -, hev⟩ := exists_eval_mulVec_eq_of_totalDegree_le A f
    have := integrable_eval_standardGaussianMeasure (f' ^ k)
    simpa [hev, Function.comp_def] using this
  exact (integrable_map_measure hc.aestronglyMeasurable hX.1).1 h1
end RegularityStructures
end
