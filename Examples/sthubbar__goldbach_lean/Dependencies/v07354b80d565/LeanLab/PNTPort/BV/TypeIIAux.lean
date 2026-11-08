module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.BV.S4Blocks
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.HeathBrown1985.DivMoments
/-!
lab proof, AI wrote this file, known mathematics, no cited input

Auxiliary bounds for the Type II sum: mean values of `Λ` and `g_v` on intervals, a
sum conversion `ℕ → ℤ`, and the square root estimate used per dyadic block.
-/
@[expose] public section
namespace LeanLab.PNTPort.BV
open Finset ArithmeticFunction
lemma sum_vonMangoldt_block (M : ℕ) :
    ∑ t ∈ Ioc M (M + M), vonMangoldt t ≤ (Real.log 4 + 4) * (2 * M) := by
  have h := Chebyshev.psi_le_const_mul_self (x := ((M + M : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at h
  calc _ ≤ ∑ t ∈ Ioc 0 (M + M), vonMangoldt t :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
          (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ _ := by push_cast at h; linarith
lemma sum_vonMangoldt_sq_block (M : ℕ) :
    ∑ t ∈ Ioc M (M + M), vonMangoldt t ^ 2 ≤
      Real.log (2 * M) * ((Real.log 4 + 4) * (2 * M)) := by
  have hl : 0 ≤ Real.log (2 * M) := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · apply Real.log_nonneg; have : (1 : ℝ) ≤ M := by exact_mod_cast h
      linarith
  calc _ ≤ ∑ t ∈ Ioc M (M + M), Real.log (2 * M) * vonMangoldt t := by
        apply sum_le_sum
        intro t ht
        have ht' := mem_Ioc.1 ht
        have h1 : vonMangoldt t ≤ Real.log (2 * M) := by
          refine vonMangoldt_le_log.trans ?_
          rcases Nat.eq_zero_or_pos t with h | h
          · simp [h]; exact hl
          · apply Real.log_le_log (by exact_mod_cast h)
            have : (t : ℝ) ≤ (M + M : ℕ) := by exact_mod_cast ht'.2
            push_cast at this; linarith
        rw [sq]
        exact mul_le_mul_of_nonneg_right h1 vonMangoldt_nonneg
    _ = Real.log (2 * M) * ∑ t ∈ Ioc M (M + M), vonMangoldt t := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_vonMangoldt_block M) hl
lemma abs_gV_le (v r : ℕ) : |gV v r| ≤ (r.divisors.card : ℝ) := by
  unfold gV; exact abs_trunc_moebius_sum_le v r
end LeanLab.PNTPort.BV
