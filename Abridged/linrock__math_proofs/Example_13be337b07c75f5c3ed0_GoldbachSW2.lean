module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_13be337b07c75f5c3ed0_GoldbachSW2 ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
set_option maxHeartbeats 4000000
/-! ### ================= SiegelTheorem.lean (verbatim, deduplicated) ================= -/
set_option maxHeartbeats 2000000
/-!
# Siegel's theorem for Dirichlet L-functions — brick-by-brick (Goldfeld's route)

Target: `siegel_zero_free`: ∀ ε > 0, ∃ c(ε) > 0, every real zero β of every L(·,χ)
(χ real nontrivial mod q) satisfies β ≤ 1 − c(ε)/q^ε. Ineffective (the dichotomy
case-split is classical); the last missing zero-free input for Siegel–Walfisz and
hence for almost-all binary Goldbach (see the approved roadmap plan).

Phase A of the roadmap; every lemma verified 0-error + `#print axioms`-clean
([propext, Classical.choice, Quot.sound]) before banking.
-/
open PowerSeries ArithmeticFunction Finset Filter
/-- A bare function packaged as an arithmetic function (forcing the value 0 at 0). -/
noncomputable def toArith (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else g n, by simp⟩

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


set_option linter.unusedVariables false in
/-- Convolving a power-bounded arithmetic function with a 1-bounded bare function
    raises the power by one (A3-g1a helper). -/
lemma conv_abs_le_pow (F : ArithmeticFunction ℝ) (k : ℕ → ℝ) (t : ℕ)
    (hF : ∀ j : ℕ, |F j| ≤ ((j:ℝ)) ^ t) (hkb : ∀ j, |k j| ≤ 1) (m : ℕ) 
    (h_toArith_apply : ∀ (g : ℕ → ℝ) (n : ℕ), n ≠ 0 → (toArith g : ℕ → ℝ) n = g n)
    :
    |(F * toArith k) m| ≤ ((m:ℝ)) ^ (t + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ArithmeticFunction.map_zero, abs_zero, Nat.cast_zero, zero_pow (by omega)]
  · have hkb' : ∀ j : ℕ, |toArith k j| ≤ 1 := by
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [toArith]
      · rw [h_toArith_apply k j (by omega)]
        exact hkb j
    rw [ArithmeticFunction.mul_apply]
    calc |∑ p ∈ m.divisorsAntidiagonal, F p.1 * toArith k p.2|
        ≤ ∑ p ∈ m.divisorsAntidiagonal, |F p.1 * toArith k p.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m.divisorsAntidiagonal, ((m:ℝ)) ^ t := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨he, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          have hp1m : p.1 ≤ m := Nat.le_of_dvd hm (Dvd.intro p.2 he)
          have hcast : ((p.1:ℝ)) ^ t ≤ ((m:ℝ)) ^ t :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hp1m) t
          rw [abs_mul]
          calc |F p.1| * |toArith k p.2| ≤ ((p.1:ℝ)) ^ t * 1 :=
                mul_le_mul (hF p.1) (hkb' p.2) (abs_nonneg _)
                  (le_trans (abs_nonneg _) (hF p.1))
            _ = ((p.1:ℝ)) ^ t := mul_one _
            _ ≤ ((m:ℝ)) ^ t := hcast
      _ = (m.divisorsAntidiagonal.card : ℝ) * ((m:ℝ)) ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((m:ℝ)) * ((m:ℝ)) ^ t := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : m.divisorsAntidiagonal.card ≤ m := by
            have hmap : ∀ p ∈ m.divisorsAntidiagonal, p.1 ∈ Icc 1 m := by
              intro p hp
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              rw [Finset.mem_Icc]
              constructor
              · by_contra h0
                push_neg at h0
                have h1 : p.1 = 0 := by omega
                rw [h1, zero_mul] at he
                omega
              · exact Nat.le_of_dvd hm (Dvd.intro p.2 he)
            have hinj : ∀ p ∈ m.divisorsAntidiagonal, ∀ p' ∈ m.divisorsAntidiagonal,
                p.1 = p'.1 → p = p' := by
              intro p hp p' hp' hfst
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              obtain ⟨he', _⟩ := Nat.mem_divisorsAntidiagonal.mp hp'
              have h1 : p.1 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at he
                omega
              have h2 : p.2 = p'.2 := by
                apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
                rw [he, hfst, he']
              exact Prod.ext hfst h2
            calc m.divisorsAntidiagonal.card ≤ (Icc 1 m).card :=
                  Finset.card_le_card_of_injOn (fun p => p.1)
                    (fun p hp => hmap p hp)
                    (fun p hp p' hp' h => hinj p hp p' hp' h)
              _ = m := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = ((m:ℝ)) ^ (t + 1) := by ring

