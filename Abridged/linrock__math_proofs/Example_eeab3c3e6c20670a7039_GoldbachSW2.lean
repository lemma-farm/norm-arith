module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_eeab3c3e6c20670a7039_GoldbachSW2 ====
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

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


set_option linter.unusedVariables false in
/-- Linear-growth sequences give absolutely convergent Abel series (A2g-c-i):
    the summability half of `lseries_eq_tsum_abel`, exposed standalone. -/
lemma abel_tsum_summable (b : ℕ → ℂ) (C : ℝ)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) 
    (h_cpow_diff_kernel_bound : ∀ (n : ℕ),
      1 ≤ n →
        ∀ (s : ℂ),
          0 < s.re →
            ‖(↑n : ℂ) ^ (-s) - (↑(n + 1) : ℂ) ^ (-s)‖ ≤
              ‖s‖ / s.re * ((↑n : ℝ) ^ (-s.re) - (↑(n + 1) : ℝ) ^ (-s.re)))
    (h_tsum_one_div_nat_rpow_le : ∀ (σ : ℝ), 1 < σ → ∑' (n : ℕ), 1 / (↑n : ℝ) ^ σ ≤ σ / (σ - 1))
    (h_weighted_telescope : ∀ (w : ℕ → ℝ) (x : ℕ),
      ∑ n ∈ Finset.Icc 1 x, (↑n : ℝ) * (w n - w (n + 1)) =
        ∑ n ∈ Finset.Icc 1 x, w n - (↑x : ℝ) * w (x + 1))
    :
    Summable (fun n : ℕ => b n * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
  have hC0 : 0 ≤ C := by
    have h0 := hb 1
    have h1 : (0:ℝ) ≤ ‖b 1‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
  have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hw]
    simp only
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
    linarith
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
  · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · apply mul_nonneg (by positivity)
        apply mul_nonneg (Nat.cast_nonneg n)
        linarith [hwanti n hn0]
    · intro x
      have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
          = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
        rw [Finset.mul_sum]
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · simp
        · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
            ext m
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      rw [hIcc, h_weighted_telescope w (x - 1)]
      have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hw]
        simp only
        positivity
      have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
        have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
          intro n hn
          obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
          rw [hw]
          simp only
          rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
        rw [Finset.sum_congr rfl hterm]
        calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
            ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
              Summable.sum_le_tsum _ (fun n _ => by positivity)
                (Real.summable_one_div_nat_rpow.mpr hs)
          _ ≤ s.re / (s.re - 1) := h_tsum_one_div_nat_rpow_le s.re hs
      have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
      apply mul_le_mul_of_nonneg_left _ hfac
      linarith [hsums, htail]
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hb0 : ‖b 0‖ = 0 := by
        have h := hb 0
        have h2 : C * ((0:ℕ):ℝ) = 0 := by norm_num
        have := norm_nonneg (b 0)
        linarith [h, h2.le, h2.ge]
      rw [norm_mul, hb0, zero_mul]
      have hrhs : (C * (‖s‖ / s.re)) * (((0:ℕ):ℝ) * (w 0 - w (0 + 1))) = 0 := by
        norm_num
      rw [hrhs]
    · rw [norm_mul]
      have h1 := hb n
      have h2 := h_cpow_diff_kernel_bound n hn0 s hσ0
      calc ‖b n‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
          ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            apply mul_le_mul h1 h2 (norm_nonneg _)
            positivity
        _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
            rw [hw]
            simp only
            push_cast
            ring

