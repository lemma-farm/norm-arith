module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib
public import Mathlib.Algebra.Order.Chebyshev

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.VanDerCorput1939.Statements ====
public section
/-!
P0067 J. G. van der Corput, Sur la démonstration de l'hypothèse de Goldbach pour les nombres
impairs, donnée par M. Vinogradow, Bull. Soc. Math. France 67 1939, supplément, 87-99,
a lecture of 8 July 1937. Read from the numdam scan, pages 87 to 94, run 20261016T2204Z-20593.
STATED: Vinogradov's asymptotic (1) to (3) for I(N), the number of ways to write odd N as a sum
of three primes, as van der Corput reports it.
PROVED, no gaps: the Euler factor identity (1 + 1/(p-1)³)(1 - 1/(p² - 3p + 3)) = 1 - 1/(p-1)²,
prime by prime; the global identity of K P(N) with the singular series is NOT formalized;
K ≥ 1; that (1) gives every large odd N as a sum of three primes; and, in Totient.lean, the
lecture's φ(q) ≥ (1/2) q^{3/4}.
Not stated: the major and minor arc estimates of pages 91 to 99, whose constants c_m, γ_i
are not explicit.
AI-written Lean code, Claude. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013.
-/
@[expose] public section
noncomputable section
namespace LeanLab.VanDerCorput1939
open Real Finset
attribute [local instance] Classical.propDecidable

/-- (3) `P(N) = ∏_{p ∣ N} (1 - 1/(p² - 3p + 3))`. -/
def P (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3))
end LeanLab.VanDerCorput1939

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_b3d95dcecfca7491ddad_SingLimit ====
/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5704, paper P0067.
P0067 van der Corput 1939: the truncated ternary singular series tends to K P(N),
uniformly over odd N. For every ε > 0 there is P₀ with
|∑_{q ≤ Q} f_N(q) - K P(N)| ≤ ε for all Q ≥ P₀ and all odd N with log N ≤ Q,
where f_N(q) = μ(q) c_q(N)/φ(q)³ is `LeanLab.PNTPort.Vinogradov.fS N q`.
The proof gives the bound e⁸/√Q + |A_Q - K| + K/(Q - 1), with A_Q the partial Euler product
of K over primes up to Q; the hypothesis log N ≤ Q is not needed and is carried only to match
the stated form. No cited input. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013. Binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.VanDerCorput1939
open Real Finset Filter Topology

attribute [local instance] Classical.propDecidable
/-- The local factor of `P(N)`. -/
def cP (N p : ℕ) : ℝ := if p ∣ N then 1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3) else 1
def BP (N Q : ℕ) : ℝ := ∏ p ∈ Nat.primesLE Q, cP N p


set_option linter.unusedVariables false in
/-- Step 5: `B_Q - P(N)` is at most `1/(Q-1)`, for odd `N`. -/
theorem BP_sub_P {N Q : ℕ} (hN : Odd N) (hQ : 2 ≤ Q) 
    (h_LeanLab_VanDerCorput1939_cP_mem : ∀ {N p : ℕ},
      Nat.Prime p → p ≠ 2 → 0 < LeanLab.VanDerCorput1939.cP N p ∧ LeanLab.VanDerCorput1939.cP N p ≤ 1)
    (h_LeanLab_VanDerCorput1939_tele_sum : ∀ (Q M : ℕ),
      Q ≤ M →
        ∑ m ∈ Finset.Icc (Q + 1) M, (1 / ((↑m : ℝ) - 2) - 1 / ((↑m : ℝ) - 1)) =
          1 / ((↑Q : ℝ) - 1) - 1 / ((↑M : ℝ) - 1))
    (h_LeanLab_VanDerCorput1939_one_sub_sum_le_prod : ∀ {ι : Type} (s : Finset ι) (a : ι → ℝ),
      (∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) → 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i))
    (h_LeanLab_VanDerCorput1939_inv_le_tele : ∀ {m : ℝ}, 3 ≤ m → 1 / (m ^ 2 - 3 * m + 3) ≤ 1 / (m - 2) - 1 / (m - 1))
    :
    0 ≤ BP N Q ∧ BP N Q ≤ 1 ∧ |BP N Q - P N| ≤ 1 / ((Q : ℝ) - 1) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact absurd hN (by decide)
  have hodd : ∀ p ∈ N.primeFactors, p ≠ 2 := by
    intro p hp e
    rw [e] at hp
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  -- `P N = ∏_{p ∣ N} cP N p`
  have hP : P N = ∏ p ∈ N.primeFactors, cP N p := by
    unfold P
    refine prod_congr rfl fun p hp => ?_
    rw [cP, if_pos (Nat.dvd_of_mem_primeFactors hp)]
  -- `B_Q = ∏_{p ∣ N, p ≤ Q} cP N p`
  have hB : BP N Q = ∏ p ∈ N.primeFactors.filter (fun p => p ≤ Q), cP N p := by
    unfold BP
    have hsub : N.primeFactors.filter (fun p => p ≤ Q) ⊆ Nat.primesLE Q := by
      intro p hp
      rw [mem_filter] at hp
      exact Nat.mem_primesLE.2 ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
    symm
    apply prod_subset hsub
    intro p hp hpn
    rw [Nat.mem_primesLE] at hp
    rw [cP, if_neg]
    intro hd
    exact hpn (mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp.2, hd, hN0⟩, hp.1⟩)
  set S := N.primeFactors.filter (fun p => ¬ p ≤ Q) with hS
  set B := BP N Q with hBdef
  set R := ∏ p ∈ S, cP N p with hR
  have hPBR : P N = B * R := by
    rw [hP, hB, hR, hS, prod_filter_mul_prod_filter_not]
  have hmem : ∀ p ∈ N.primeFactors, 0 < cP N p ∧ cP N p ≤ 1 := fun p hp =>
    h_LeanLab_VanDerCorput1939_cP_mem (Nat.prime_of_mem_primeFactors hp) (hodd p hp)
  have hB0 : 0 ≤ B := by
    rw [hB]; exact prod_nonneg fun p hp => (hmem p (mem_filter.1 hp).1).1.le
  have hB1 : B ≤ 1 := by
    rw [hB]; exact prod_le_one₀ (fun p hp => (hmem p (mem_filter.1 hp).1).1.le)
      (fun p hp => (hmem p (mem_filter.1 hp).1).2)
  have hR1 : R ≤ 1 := prod_le_one₀ (fun p hp => (hmem p (mem_filter.1 hp).1).1.le)
      (fun p hp => (hmem p (mem_filter.1 hp).1).2)
  -- lower bound on `R`
  have hS3 : ∀ p ∈ S, (3 : ℝ) ≤ p ∧ (Q : ℝ) + 1 ≤ p := by
    intro p hp
    rw [hS, mem_filter] at hp
    have : Q + 1 ≤ p := by omega
    constructor
    · exact_mod_cast (by omega : 3 ≤ p)
    · exact_mod_cast this
  have hRlow : 1 - 1 / ((Q : ℝ) - 1) ≤ R := by
    have hRe : R = ∏ p ∈ S, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3)) := by
      rw [hR]
      refine prod_congr rfl fun p hp => ?_
      rw [cP, if_pos (Nat.dvd_of_mem_primeFactors (mem_filter.1 hp).1)]
    rw [hRe]
    refine le_trans ?_ (h_LeanLab_VanDerCorput1939_one_sub_sum_le_prod S _ ?_)
    · have hsum : ∑ p ∈ S, 1 / ((p : ℝ) ^ 2 - 3 * p + 3) ≤ 1 / ((Q : ℝ) - 1) := by
        calc ∑ p ∈ S, 1 / ((p : ℝ) ^ 2 - 3 * p + 3)
            ≤ ∑ p ∈ S, (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) :=
              sum_le_sum fun p hp => h_LeanLab_VanDerCorput1939_inv_le_tele (hS3 p hp).1
          _ ≤ ∑ m ∈ Icc (Q + 1) (max N Q), (1 / ((m : ℝ) - 2) - 1 / ((m : ℝ) - 1)) := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rw [hS, mem_filter] at hp
                have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0)
                  (Nat.dvd_of_mem_primeFactors hp.1)
                rw [mem_Icc]; constructor <;> omega
              · intro m hm _
                rw [mem_Icc] at hm
                have : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
                have h1 : 0 < (m : ℝ) - 2 := by linarith
                rw [sub_nonneg]
                apply one_div_le_one_div_of_le h1; linarith
          _ = 1 / ((Q : ℝ) - 1) - 1 / (((max N Q : ℕ) : ℝ) - 1) :=
              h_LeanLab_VanDerCorput1939_tele_sum Q _ (le_max_right _ _)
          _ ≤ 1 / ((Q : ℝ) - 1) := by
              have : (2 : ℝ) ≤ ((max N Q : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ max N Q)
              have : 0 ≤ 1 / (((max N Q : ℕ) : ℝ) - 1) := by
                apply div_nonneg zero_le_one; linarith
              linarith
      linarith
    · intro p hp
      have h3 := (hS3 p hp).1
      have hd : 1 < (p : ℝ) ^ 2 - 3 * p + 3 := by nlinarith
      constructor
      · apply div_nonneg zero_le_one; linarith
      · rw [div_le_one (by linarith)]; linarith
  refine ⟨hB0, hB1, ?_⟩
  rw [hPBR, show B - B * R = B * (1 - R) by ring, abs_of_nonneg (mul_nonneg hB0 (by linarith))]
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have : 0 ≤ 1 - R := by linarith
  calc B * (1 - R) ≤ 1 * (1 - R) := mul_le_mul_of_nonneg_right hB1 this
    _ ≤ 1 / ((Q : ℝ) - 1) := by linarith
end LeanLab.VanDerCorput1939
