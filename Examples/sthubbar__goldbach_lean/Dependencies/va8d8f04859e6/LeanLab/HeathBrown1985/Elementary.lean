module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Statements
/-!
P0096 Heath-Brown 1985, elementary inputs for the deduction of Theorem 2 on page 52 to 53.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
attribute [local instance] Classical.propDecidable
/-- A finset of positive integers has reciprocal sum at most the harmonic sum of its size. -/
theorem sum_inv_le_harmonic (S : Finset ℕ) (hS : ∀ s ∈ S, 1 ≤ s) :
    ∑ s ∈ S, (s : ℝ)⁻¹ ≤ ∑ j ∈ Icc 1 S.card, (j : ℝ)⁻¹ := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ih' := ih (fun t ht => hS t (mem_insert_of_mem ht))
    have ha1 : 1 ≤ a := hS a (mem_insert_self a s)
    have hsub : s ⊆ Icc 1 (a - 1) := by
      intro t ht
      have := hS t (mem_insert_of_mem ht)
      have := hlt t ht
      simp only [mem_Icc]; omega
    have hcard : s.card + 1 ≤ a := by
      have := card_le_card hsub
      simp at this; omega
    rw [sum_insert ha, card_insert_of_notMem ha, sum_Icc_succ_top (by omega)]
    have : (a : ℝ)⁻¹ ≤ ((s.card + 1 : ℕ) : ℝ)⁻¹ := by
      apply inv_anti₀ (by positivity); exact_mod_cast hcard
    linarith
theorem sum_inv_Icc_le_log (n : ℕ) : ∑ j ∈ Icc 1 n, (j : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  simpa [harmonic_eq_sum_Icc] using this
/-- `ω(k) log 2 ≤ log k`. -/
theorem card_primeFactors_mul_log_two_le (k : ℕ) (hk : 1 ≤ k) :
    (k.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log k := by
  have h1 : 2 ^ k.primeFactors.card ≤ ∏ p ∈ k.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ k.primeFactors, p ≤ k := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd k)
  have h3 : ((2 : ℕ) : ℝ) ^ k.primeFactors.card ≤ (k : ℝ) := by exact_mod_cast h1.trans h2
  have := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at this
  simpa using this
/-- `k / φ(k) ≤ e (1 + ω(k))`. -/
theorem div_totient_le (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) / (Nat.totient k : ℝ) ≤ Real.exp 1 * (1 + k.primeFactors.card) := by
  have hφ : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hP : ∀ p ∈ k.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have key := Nat.totient_mul_prod_primeFactors k
  have keyR : (Nat.totient k : ℝ) * ∏ p ∈ k.primeFactors, (p : ℝ) =
      (k : ℝ) * ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    push_cast at this
    rw [this]
    congr 1
    apply prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  have hpos : (0 : ℝ) < ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  have hratio : (k : ℝ) / (Nat.totient k : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
    linarith [keyR]
  rw [hratio]
  have hexp : ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp; have := hP p hp; apply div_nonneg <;> linarith
    · intro p hp
      have h2 := hP p hp
      have : (p : ℝ) / ((p : ℝ) - 1) = ((p : ℝ) - 1)⁻¹ + 1 := by
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      rw [this]; exact Real.add_one_le_exp _
  have hsum : ∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹ ≤ 1 + Real.log k.primeFactors.card := by
    have hinj : Set.InjOn (fun p : ℕ => p - 1) (k.primeFactors : Set ℕ) := by
      intro a ha b hb hab
      have := (Nat.prime_of_mem_primeFactors ha).one_le
      have := (Nat.prime_of_mem_primeFactors hb).one_le
      simp at hab; omega
    have e1 : ∑ p ∈ k.primeFactors, ((p : ℝ) - 1)⁻¹ =
        ∑ s ∈ k.primeFactors.image (fun p : ℕ => p - 1), (s : ℝ)⁻¹ := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).one_le
      push_cast [this]; ring
    rw [e1]
    have h1 := sum_inv_le_harmonic (k.primeFactors.image (fun p : ℕ => p - 1)) (by
      intro s hs
      simp only [mem_image] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega)
    rw [card_image_of_injOn hinj] at h1
    exact h1.trans (sum_inv_Icc_le_log _)
  calc _ ≤ _ := hexp
    _ ≤ Real.exp (1 + Real.log k.primeFactors.card) := Real.exp_le_exp.mpr hsum
    _ ≤ Real.exp 1 * (1 + k.primeFactors.card) := by
      rw [Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      rcases Nat.eq_zero_or_pos k.primeFactors.card with h | h
      · simp [h]
      · rw [Real.exp_log (by exact_mod_cast h)]; linarith
end LeanLab.HeathBrown1985
