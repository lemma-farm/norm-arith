import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.v3660e7e055f3.ShiuFoundation
import Mathlib.Data.Nat.Choose.Bounds
/-!
# Kernel-checked analytic hypotheses for the divisor-square weight

This file proves elementary growth facts which are genuine hypotheses in
Shiu's theorem.  It does not postulate or claim the progression estimate or
Mertens' theorem.
-/
namespace ShiuAnalyticLayer
open ArithmeticFunction MixedMellinCert ShiuFoundation
open scoped ArithmeticFunction.zeta BigOperators
noncomputable section
/-- A polynomial bound in the prime-power exponent. -/
theorem multichoose_le_add_pow (k e : ℕ) (hk : 1 ≤ k) :
    k.multichoose e ≤ (e + k) ^ k := by
  rw [Nat.multichoose_eq]
  have htop : k + e - 1 = e + (k - 1) := by omega
  rw [htop, Nat.choose_symm_add]
  refine (Nat.choose_le_pow _ _).trans ?_
  calc
    (e + (k - 1)) ^ (k - 1) ≤ (e + k) ^ (k - 1) :=
      Nat.pow_le_pow_left (by omega) _
    _ ≤ (e + k) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
/-- A fully explicit form of polynomial-versus-exponential domination. -/
theorem add_pow_le_exp (k m e : ℕ) (hk : 1 ≤ k) :
    (e + k) ^ m ≤
      (k ^ m * m.factorial * 2 ^ m) * 2 ^ e := by
  calc
    (e + k) ^ m ≤ (k * (e + 1)) ^ m :=
      Nat.pow_le_pow_left (by nlinarith) _
    _ = k ^ m * (e + 1) ^ m := by rw [mul_pow]
    _ ≤ k ^ m * (e + 1).ascFactorial m := by
      gcongr
      exact Nat.pow_succ_le_ascFactorial (e + 1) m
    _ = k ^ m * (m.factorial * (e + m).choose m) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
    _ ≤ k ^ m * (m.factorial * 2 ^ (e + m)) := by
      gcongr
      exact Nat.choose_le_two_pow _ _
    _ = (k ^ m * m.factorial * 2 ^ m) * 2 ^ e := by
      rw [pow_add]
      ring
/-- Uniform local domination by `2^e`; unlike the earlier `k^(2e)` bound,
the constant here is independent of the exponent. -/
theorem multichoose_square_pow_le_const_mul_two_pow
    (k d e : ℕ) (hk : 1 ≤ k) :
    (k.multichoose e ^ 2) ^ d ≤
      (k ^ (2 * k * d) * (2 * k * d).factorial * 2 ^ (2 * k * d)) * 2 ^ e := by
  calc
    (k.multichoose e ^ 2) ^ d = k.multichoose e ^ (2 * d) := by
      rw [← pow_mul]
    _ ≤ ((e + k) ^ k) ^ (2 * d) :=
      Nat.pow_le_pow_left (multichoose_le_add_pow k e hk) _
    _ = (e + k) ^ (2 * k * d) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (k ^ (2 * k * d) * (2 * k * d).factorial * 2 ^ (2 * k * d)) * 2 ^ e :=
      add_pow_le_exp k (2 * k * d) e hk
theorem tauAF_square_prime_pow_pow_le
    (k d p e : ℕ) (hp : p.Prime) (hlarge : (k * k) ^ d ≤ p) :
    (tauAF k (p ^ e) ^ 2) ^ d ≤ p ^ e := by
  calc
    (tauAF k (p ^ e) ^ 2) ^ d ≤ (((k * k) ^ e) ^ d) :=
      Nat.pow_le_pow_left (tauAF_square_prime_pow_le k e p hp) _
    _ = ((k * k) ^ d) ^ e := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ p ^ e := Nat.pow_le_pow_left hlarge _
/-- At most `T` members of a finite set can lie below `T`; consequently a
constant paid only at those members contributes at most its `T`-th power. -/
theorem prod_if_lt_le_pow (s : Finset ℕ) (A T : ℕ) (hA : 0 < A) :
    (∏ p ∈ s, if p < T then A else 1) ≤ A ^ T := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  apply Nat.pow_le_pow_right hA
  have hsubset : {p ∈ s | p < T} ⊆ Finset.range T := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  simpa using Finset.card_le_card hsubset
/-- Rational-moment form of fixed-`k` subpower growth.  For every positive
denominator `d`, the `d`-th power of `tau_k(n)^2` is bounded by a constant
times `n`.  This is the integer statement behind the condition
`tau_k(n)^2 ≪_{k,ε} n^ε`. -/
theorem tauAF_square_subpower_moment (k d : ℕ) (hk : 1 ≤ k) (_hd : 1 ≤ d) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → (tauAF k n ^ 2) ^ d ≤ C * n := by
  classical
  let m : ℕ := 2 * k * d
  let A : ℕ := k ^ m * m.factorial * 2 ^ m
  let T : ℕ := (k * k) ^ d
  refine ⟨A ^ T, pow_pos ?_ _, ?_⟩
  · dsimp [A]
    positivity
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [tauAF_eq_factorization_prod k n hn0]
  change ((∏ p ∈ n.factorization.support,
    k.multichoose (n.factorization p)) ^ 2) ^ d ≤ A ^ T * n
  rw [← pow_mul, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.factorization.support,
        k.multichoose (n.factorization p) ^ (2 * d)) =
        ∏ p ∈ n.factorization.support,
          (k.multichoose (n.factorization p) ^ 2) ^ d := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [← pow_mul]
    _ ≤ ∏ p ∈ n.factorization.support,
          (if p < T then A else 1) * p ^ n.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
      split_ifs with hsmall
      · calc
          (k.multichoose (n.factorization p) ^ 2) ^ d ≤
              A * 2 ^ n.factorization p := by
                simpa [A, m] using
                  multichoose_square_pow_le_const_mul_two_pow
                    k d (n.factorization p) hk
          _ ≤ A * p ^ n.factorization p := by
                exact Nat.mul_le_mul_left A
                  (Nat.pow_le_pow_left hpprime.two_le _)
      · rw [← tauAF_prime_pow_eq_multichoose k (n.factorization p) p hpprime]
        simpa only [one_mul] using
          tauAF_square_prime_pow_pow_le k d p (n.factorization p) hpprime
            (by simpa [T] using Nat.le_of_not_gt hsmall)
    _ = (∏ p ∈ n.factorization.support, if p < T then A else 1) *
          (∏ p ∈ n.factorization.support, p ^ n.factorization p) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ A ^ T * (∏ p ∈ n.factorization.support, p ^ n.factorization p) := by
      gcongr
      exact prod_if_lt_le_pow n.factorization.support A T (by
        dsimp [A]
        positivity)
    _ = A ^ T * n := by
      rw [← Finsupp.prod]
      exact congrArg (A ^ T * ·) (Nat.prod_factorization_pow_eq_self hn0)
/-- The usual real-exponent form of Shiu's subpower hypothesis for the
literal square weight.  Its proof is reduced to the preceding integer moment
bound, so no analytic number-theory estimate is hidden here. -/
theorem tauAF_square_subpolynomial (k : ℕ) (hk : 1 ≤ k) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        (tauAF k n ^ 2 : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  let d : ℕ := q + 1
  have hd : 1 ≤ d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hinv : ((d : ℝ)⁻¹) ≤ ε := by
    have : (1 : ℝ) / (d : ℝ) < ε := by
      simpa [d, Nat.cast_add] using hq
    simpa [one_div] using this.le
  obtain ⟨C₀, hC₀, hbound⟩ := tauAF_square_subpower_moment k d hk hd
  let C : ℝ := (C₀ : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos (by exact_mod_cast hC₀) _
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnat := hbound n hn
  have hroot : (tauAF k n ^ 2 : ℝ) ≤
      ((C₀ : ℝ) * (n : ℝ)) ^ ((d : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hdpos).2
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  calc
    (tauAF k n ^ 2 : ℝ) ≤ ((C₀ : ℝ) * (n : ℝ)) ^ ((d : ℝ)⁻¹) := hroot
    _ = C * (n : ℝ) ^ ((d : ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ C * (n : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow_of_exponent_le (by
        exact_mod_cast (show 1 ≤ n by omega)) hinv
/-! ## Exact Shiu weight hypotheses -/
end
end ShiuAnalyticLayer
