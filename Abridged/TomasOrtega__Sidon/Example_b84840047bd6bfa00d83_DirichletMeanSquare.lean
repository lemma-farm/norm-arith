module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic

-- ==== Examples.TomasOrtega__Sidon.Examples.Example_b84840047bd6bfa00d83_DirichletMeanSquare ====
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Finite mean squares of Dirichlet polynomials -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace Sidon
/-- The additive character at an arbitrary real frequency, without a `2π` factor. -/
def frequencyChar (ω t : ℝ) : ℂ := Complex.exp ((ω : ℂ) * t * Complex.I)

/-- A finite Dirichlet polynomial is obtained by setting `ω n = -log n`. -/
def finiteFrequencySum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ)
    (t : ℝ) : ℂ := ∑ i ∈ s, a i * frequencyChar (ω i) t


set_option linter.unusedVariables false in
/-- Diagonal integration is exact; every distinct frequency costs its reciprocal gap. -/
theorem integral_finiteFrequencySum_norm_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ) (hω : Set.InjOn ω (s : Set ι)) 
    (h_Sidon_norm_integral_frequencyChar_le : ∀ {ω : ℝ}, ω ≠ 0 → ∀ (T : ℝ), ‖∫ (t : ℝ) in 0..T, Sidon.frequencyChar ω t‖ ≤ 2 / |ω|)
    (h_Sidon_integral_finiteFrequencySum_norm_sq : ∀ {ι : Type u_1} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ),
      ∫ (t : ℝ) in 0..T, ‖Sidon.finiteFrequencySum s a ω t‖ ^ 2 =
        (∑ i ∈ s,
            ∑ j ∈ s,
              a i * (starRingEnd ℂ : ℂ → ℂ) (a j) *
                ∫ (t : ℝ) in 0..T, Sidon.frequencyChar (ω i - ω j) t).re)
    (h_Sidon_frequencyChar_zero : ∀ (t : ℝ), Sidon.frequencyChar 0 t = 1)
    :
    (∫ t in (0 : ℝ)..T, ‖finiteFrequencySum s a ω t‖ ^ 2) ≤
      T * ∑ i ∈ s, ‖a i‖ ^ 2 +
        ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else
          2 * ‖a i‖ * ‖a j‖ / |ω i - ω j| := by
  classical
  rw [h_Sidon_integral_finiteFrequencySum_norm_sq]
  simp only [Complex.re_sum]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ((a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t).re ≤
        (if i = j then T * ‖a i‖ ^ 2 else 0) +
        (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, h_Sidon_frequencyChar_zero, intervalIntegral.integral_const,
        sub_zero, Complex.real_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        ite_true, add_zero]
      simp [← Complex.ofReal_pow, mul_comm]
    · simp only [hij, ite_false, zero_add]
      have hgap : ω i - ω j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hω hi hj h))
      calc
        _ ≤ ‖(a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ :=
          Complex.re_le_norm _
        _ = (‖a i‖ * ‖a j‖) * ‖∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
        _ ≤ (‖a i‖ * ‖a j‖) * (2 / |ω i - ω j|) :=
          mul_le_mul_of_nonneg_left (h_Sidon_norm_integral_frequencyChar_le hgap T) (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((if i = j then T * ‖a i‖ ^ 2 else 0) +
         (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      exact hpair i hi
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
end Sidon
