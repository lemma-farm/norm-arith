module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_05e162abbcc24fc7c334_GoldbachSW2 ====
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
/-- **The partial-sum series representation** (Siegel brick A2g-ii): for linearly
    bounded partial sums `‖A(x)‖ ≤ Cx` and `Re s > 1`,
    `Σ' n, a(n)n^{−s} = Σ' n, A(n)(n^{−s} − (n+1)^{−s})` — the boundary term
    `A(x)x^{−s}` dies and the Abel-rearranged series converges to the L-series. -/
theorem lseries_eq_tsum_abel (a : ℕ → ℂ) (C : ℝ)
    (hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) 
    (h_abel_initial : ∀ (a w : ℕ → ℂ) (x : ℕ),
      1 ≤ x →
        ∑ n ∈ Finset.Icc 1 x, a n * w n =
          (∑ n ∈ Finset.Icc 1 x, a n) * w x +
            ∑ n ∈ Finset.Icc 1 (x - 1), (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n + 1)))
    (h_tsum_one_div_nat_rpow_le : ∀ (σ : ℝ), 1 < σ → ∑' (n : ℕ), 1 / (↑n : ℝ) ^ σ ≤ σ / (σ - 1))
    (h_weighted_telescope : ∀ (w : ℕ → ℝ) (x : ℕ),
      ∑ n ∈ Finset.Icc 1 x, (↑n : ℝ) * (w n - w (n + 1)) =
        ∑ n ∈ Finset.Icc 1 x, w n - (↑x : ℝ) * w (x + 1))
    (h_cpow_diff_kernel_bound : ∀ (n : ℕ),
      1 ≤ n →
        ∀ (s : ℂ),
          0 < s.re →
            ‖(↑n : ℂ) ^ (-s) - (↑(n + 1) : ℂ) ^ (-s)‖ ≤
              ‖s‖ / s.re * ((↑n : ℝ) ^ (-s.re) - (↑(n + 1) : ℝ) ^ (-s.re)))
    :
    LSeries a s
      = ∑' n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  -- the partial sums of the L-series along Icc 1 x
  have hterm_eq : ∀ n : ℕ, 1 ≤ n → LSeries.term a s n = a n * ((n:ℂ)) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hpartial : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
      atTop (nhds (LSeries a s)) := by
    have h1 : Tendsto (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n)
        atTop (nhds (LSeries a s)) := by
      have := hsum.hasSum.tendsto_sum_nat
      exact this.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ x : ℕ, ∑ n ∈ range (x + 1), LSeries.term a s n
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s) := by
      intro x
      rw [show range (x + 1) = insert 0 (Icc 1 x) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [LSeries.term_zero, zero_add]
      exact Finset.sum_congr rfl (fun n hn => hterm_eq n (Finset.mem_Icc.mp hn).1)
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
        = (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n) from
      funext (fun x => (h2 x).symm)]
    exact h1
  -- boundary decay: A(x)·x^{−s} → 0
  have hboundary : Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s))
      atTop (nhds 0) := by
    have hC0 : 0 ≤ C := by
      have h0 := hC 1
      have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
      have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
      linarith [h0, h1, h2.le, h2.ge]
    have hbnd : ∀ x : ℕ, ‖(∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s)‖
        ≤ C * ((x:ℝ)) ^ (1 - s.re) := by
      intro x
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
          Finset.sum_empty, zero_mul, norm_zero, Nat.cast_zero,
          Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0), mul_zero]
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hx0, Complex.neg_re]
        have hxr : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx0
        calc ‖∑ n ∈ Icc 1 x, a n‖ * ((x:ℝ)) ^ (-s.re)
            ≤ (C * x) * ((x:ℝ)) ^ (-s.re) := by
              apply mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg hxr.le _)
          _ = C * ((x:ℝ)) ^ (1 - s.re) := by
              rw [show (1:ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hxr,
                Real.rpow_one]
              ring
    have hg0 : Tendsto (fun x : ℕ => C * ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℕ => ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := this.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      simpa using h1.const_mul C
    exact squeeze_zero_norm hbnd hg0
  -- Abel + limits
  have hAbel : ∀ x : ℕ, 1 ≤ x →
      ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
        - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
    intro x hx
    have := h_abel_initial a (fun n => ((n:ℂ)) ^ (-s)) x hx
    push_cast at this ⊢
    linear_combination -this
  have hlim : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop (nhds (LSeries a s)) := by
    have heq : ∀ᶠ x : ℕ in atTop, ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
          - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      exact hAbel x hx
    rw [Filter.tendsto_congr' heq]
    have := hpartial.sub hboundary
    simpa using this
  -- absolute convergence via the real difference kernel
  have hC0' : 0 ≤ C := by
    have h0 := hC 1
    have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  have hsummable : Summable (fun n : ℕ => (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
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
      · simp
      · rw [norm_mul]
        have h1 := hC n
        have h2 := h_cpow_diff_kernel_bound n hn0 s hσ0
        calc ‖∑ m ∈ Icc 1 n, a m‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
            ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
              apply mul_le_mul h1 h2 (norm_nonneg _)
              positivity
          _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
              rw [hw]
              simp only
              push_cast
              ring
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hIccrange : ∀ x : ℕ, ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, zero_mul, zero_add]
  have hrange' : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop
      (nhds (∑' n : ℕ, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) := by
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        = (fun x : ℕ => ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) from
      funext (fun x => (hIccrange x).symm)]
    exact hrange
  exact (tendsto_nhds_unique hrange' hlim).symm
