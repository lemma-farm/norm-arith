module
public import Mathlib
@[expose] public section
/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
These generic results are separated from the unproved determinant power-series bridge.
-/
noncomputable section
open scoped BigOperators
namespace RoughRegime.SeriesBounds
def convolution {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2
/-- Adding one reciprocal factor increases the polynomial coefficient weight by one.
This proves the counting estimate in Lemma 5(a) without using eigenvalue-defined polynomials. -/
theorem convolution_coefficient_bound {R : Type*} [NormedRing R]
    (f g : ℕ → R) (ν k : ℕ) (ρ A B : ℝ) (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ A * ((i + 1 : ℕ) : ℝ) ^ ν * ρ ^ i)
    (hg : ∀ j : ℕ, ‖g j‖ ≤ B * ρ ^ j) :
    ‖convolution f g k‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ (ν + 1) * ρ ^ k := by
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      ‖f ij.1 * g ij.2‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
    have he : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hle : ij.1 + 1 ≤ k + 1 := by omega
    have hpow : (((ij.1 + 1 : ℕ) : ℝ)) ^ ν ≤ ((k + 1 : ℕ) : ℝ) ^ ν :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) ν
    have hnorm := (norm_mul_le (f ij.1) (g ij.2)).trans
      (mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) (by positivity))
    calc
      _ ≤ (A * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ ij.1) * (B * ρ ^ ij.2) := hnorm
      _ = A * B * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by rw [← he, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hB)) (pow_nonneg hp.le k)
  unfold convolution
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, ‖f ij.1 * g ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; rw [pow_succ]; ring
end RoughRegime.SeriesBounds
