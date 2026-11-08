import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourcePolynomialR11
import Mathlib
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
/-- The recurrence specialises to the ordinary binomial coefficient at q=1. -/
theorem gaussian_at_one {R : Type*} [CommRing R] (n k : ℕ) :
    gaussBinom (1 : R) n k = (n.choose k : R) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussBinom_succ, Nat.choose_succ_succ, Nat.cast_add, ih, ih]
          by_cases hk : k ≤ n
          · simp [hk, add_comm]
          · have hkn : n < k := Nat.lt_of_not_ge hk
            simp [hk, Nat.choose_eq_zero_of_lt hkn]
theorem gaussian_monic_natDegree (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).Monic ∧
      (gaussBinom (X : ℤ[X]) n k).natDegree = k * (n - k) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases heq : k = n
          · subst k
            simp [gaussBinom_self]
          · have hlt : k < n := by omega
            obtain ⟨hL, hdL⟩ := ih (k + 1) (by omega)
            obtain ⟨hG, hdG⟩ := ih k hkn
            have hR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).Monic :=
              (monic_X_pow (n - k)).mul hG
            have hdR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree =
                (n - k) + k * (n - k) := by
              rw [natDegree_mul' (by simp [hG.leadingCoeff]), natDegree_X_pow, hdG]
            have hsub : n - (k + 1) + 1 = n - k := by omega
            have hdeglt : (gaussBinom (X : ℤ[X]) n (k + 1)).natDegree <
                ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree := by
              rw [hdL, hdR]
              nlinarith
            rw [gaussBinom_succ_of_le X hkn]
            constructor
            · change (_ + _ : ℤ[X]).leadingCoeff = 1
              rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hdeglt), hR.leadingCoeff]
            · rw [natDegree_add_eq_right_of_natDegree_lt hdeglt, hdR]
              have hsub' : n + 1 - (k + 1) = n - k := by omega
              rw [hsub']
              ring
theorem gaussian_polynomial_natDegree (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).natDegree = k * (n - k) :=
  (gaussian_monic_natDegree n k hk).2
noncomputable def integerCoefficientMass (p : ℤ[X]) : ℤ :=
  ∑ d ∈ p.support, |p.coeff d|
/-- Exact l1 mass, including the out-of-range zero Gaussian. -/
theorem gaussian_coefficient_mass (n k : ℕ) :
    integerCoefficientMass (gaussBinom (X : ℤ[X]) n k) = (n.choose k : ℤ) := by
  have heval : (gaussBinom (X : ℤ[X]) n k).eval 1 = (n.choose k : ℤ) := by
    simpa [gaussian_at_one] using (eval₂_gaussBinom (1 : ℤ) n k)
  rw [← heval, eval_eq_sum]
  unfold integerCoefficientMass Polynomial.sum
  apply Finset.sum_congr rfl
  intro d hd
  simp only [one_pow, mul_one]
  exact abs_of_nonneg (gaussian_coefficient_bounds n k d).1
/-- The exponential l1 bound has no missing degree factor. -/
theorem gaussian_coefficient_mass_le (n k : ℕ) :
    integerCoefficientMass (gaussBinom (X : ℤ[X]) n k) ≤ (2 : ℤ) ^ n := by
  rw [gaussian_coefficient_mass]
  exact_mod_cast choose_le_two_pow n k
def sourceASummandDegree (n s : ℕ) : ℕ :=
  sourceM n + sourceAExponent n s +
    12 * n * (2 * n + s) + (13 * n - s) * s
lemma sourceASummandDegree_succ (n s : ℕ) (hs : s < 13 * n) :
    sourceASummandDegree n (s + 1) = sourceASummandDegree n s + (26 * n - s) := by
  have hsub : 13 * n - (s + 1) + 1 = 13 * n - s := by omega
  have hsub2 : 26 * n - s + s = 26 * n := by omega
  unfold sourceASummandDegree sourceAExponent
  rw [choose_two_succ]
  rw [← hsub, ← hsub2]
  ring_nf
  omega
/-- No cancellation of the top degree is possible in the full alternating sum. -/
theorem sourceASummandDegree_strict (n : ℕ) {s t : ℕ}
    (hst : s < t) (ht : t ≤ 13 * n) :
    sourceASummandDegree n s < sourceASummandDegree n t := by
  induction t with
  | zero => omega
  | succ t ih =>
      have ht' : t < 13 * n := by omega
      have hstep : sourceASummandDegree n t < sourceASummandDegree n (t + 1) := by
        rw [sourceASummandDegree_succ n t ht']
        have hpos : 0 < 26 * n - t := by omega
        omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hst with hst' | rfl
      · exact (ih hst' (by omega)).trans hstep
      · exact hstep
lemma twice_choose_two_nat (s : ℕ) : 2 * s.choose 2 + s = s * s := by
  have h := twice_choose_two_int s
  have hi : (2 : ℤ) * (s.choose 2 : ℤ) + (s : ℤ) = (s : ℤ) * (s : ℤ) := by
    nlinarith
  exact_mod_cast hi
/-- The printed K is integral; natural division here is justified below. -/
def sourceK (n : ℕ) : ℕ := (1091 * n ^ 2 + 81 * n + 2) / 2
lemma sourceASummandDegree_last (n : ℕ) : sourceASummandDegree n (13 * n) = sourceK n := by
  have hc := twice_choose_two_nat (13 * n)
  have hd : 2 * sourceASummandDegree n (13 * n) = 1091 * n ^ 2 + 81 * n + 2 := by
    unfold sourceASummandDegree sourceAExponent sourceM
    simp only [Nat.sub_self, zero_mul, add_zero]
    nlinarith
  unfold sourceK
  omega
end ErdosProblems.Erdos1049.PaperR12
