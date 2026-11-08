module
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000
open DirichletCharacter Complex
open intervalIntegral in
/-- **The Abel kernel inequality**: `‖n^{−s} − (n+1)^{−s}‖ ≤ (‖s‖/σ)(n^{−σ} − (n+1)^{−σ})`
    for `σ = Re s > 0` — the summand bound that turns bounded character sums into the
    uniform polynomial growth of `L(s,χ)` by partial summation. -/
lemma cpow_diff_kernel_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re) :
    ‖((n : ℂ)) ^ (-s) - (((n + 1 : ℕ) : ℂ)) ^ (-s)‖
      ≤ (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hab : (n:ℝ) ≤ ((n+1 : ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
  have h0notin : (0:ℝ) ∉ Set.uIcc ((n:ℝ)) (((n+1 : ℕ)):ℝ) := by
    rw [Set.uIcc_of_le hab]
    intro h0
    rw [Set.mem_Icc] at h0
    linarith [h0.1]
  -- FTC via integral_cpow at r = −s−1
  have hr : (-s - 1 : ℂ) ≠ -1 := by
    intro h
    apply hs0
    have : -s = 0 := by linear_combination h
    linear_combination -this
  have hint := integral_cpow (a := (n:ℝ)) (b := ((n+1 : ℕ):ℝ)) (r := -s - 1)
    (Or.inr ⟨hr, h0notin⟩)
  have hexp : (-s - 1 : ℂ) + 1 = -s := by ring
  rw [hexp] at hint
  have hFTC : ((n : ℂ)) ^ (-s) - (((n + 1 : ℕ) : ℂ)) ^ (-s)
      = s * ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1) := by
    rw [hint]
    have hcast1 : (((n:ℝ)) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; rfl
    have hcast2 : ((((n+1 : ℕ)):ℝ) : ℂ) = (((n+1) : ℕ) : ℂ) := by push_cast; rfl
    rw [hcast1, hcast2]
    field_simp
    ring
  rw [hFTC, norm_mul]
  -- bound the integral
  have hnorm_int : ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
      ≤ ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1) := by
    have h1 : ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
        ≤ ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ‖((x:ℂ)) ^ (-s - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have h2 : ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ‖((x:ℂ)) ^ (-s - 1)‖
        = ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      dsimp only
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hreal : ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1)
      = ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re := by
    have hrne : (-s.re - 1 : ℝ) ≠ -1 := by
      intro h
      have : s.re = 0 := by linarith
      linarith
    have h := integral_rpow (a := (n:ℝ)) (b := ((n+1 : ℕ):ℝ)) (r := -s.re - 1)
      (Or.inr ⟨hrne, h0notin⟩)
    rw [show (-s.re - 1 : ℝ) + 1 = -s.re by ring] at h
    rw [h]
    field_simp
    ring
  rw [hreal] at hnorm_int
  have hσne : s.re ≠ 0 := hσ.ne'
  have hmono : 0 ≤ ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    have h1 : ((n + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-s.re) := by
      apply Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
    linarith
  calc ‖s‖ * ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
      ≤ ‖s‖ * (((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re) :=
        mul_le_mul_of_nonneg_left hnorm_int (norm_nonneg s)
    _ = (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
        field_simp
lemma tsum_one_div_nat_rpow_le (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ σ ≤ σ / (σ - 1) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  have hσ1' : (0:ℝ) < σ - 1 := by linarith
  have hmaj : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- N = 0 or 1: sum is 0
    interval_cases N
    · simp
      positivity
    · rw [Finset.sum_range_one, Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
      positivity
  · -- N ≥ 2: peel n = 0, 1 and integral-compare the rest
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2) hN]
    have hhead : ∑ i ∈ Finset.Ico (0:ℕ) 2, 1 / (i : ℝ) ^ σ = 1 := by
      rw [Nat.Ico_zero_eq_range]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero, zero_add]
      norm_num
    have htail : ∑ i ∈ Finset.Ico 2 N, 1 / (i : ℝ) ^ σ ≤ 1 / (σ - 1) := by
      have hshift : ∑ i ∈ Finset.Ico 2 N, 1 / (i : ℝ) ^ σ
          = ∑ i ∈ Finset.Ico 1 (N - 1), (fun x : ℝ => x ^ (-σ)) ((i + 1 : ℕ) : ℝ) := by
        rw [show (2:ℕ) = 1 + 1 by rfl, show N = (N - 1) + 1 by omega]
        rw [← Finset.sum_Ico_add]
        apply Finset.sum_congr rfl
        intro i hi
        simp only
        rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]
        congr 2
        push_cast
        ring
      rw [hshift]
      have hab : (1:ℕ) ≤ N - 1 := by omega
      have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc ((1:ℕ):ℝ) ((N-1:ℕ):ℝ)) := by
        intro x hx y hy hxy
        simp only
        have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos (by exact_mod_cast hx.1)
        have hy0 : (0:ℝ) < y := lt_of_lt_of_le hx0 hxy
        rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hx0 σ)
          (Real.rpow_le_rpow hx0.le hxy hσ0.le)
      have hint := AntitoneOn.sum_le_integral_Ico hab hanti
      apply le_trans hint
      have hN1 : ((1:ℕ):ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hab
      have h0mem : (0:ℝ) ∉ Set.uIcc ((1:ℕ):ℝ) ((N-1:ℕ):ℝ) := by
        rw [Set.uIcc_of_le hN1]
        rintro ⟨h0, -⟩
        norm_num at h0
      rw [integral_rpow (Or.inr ⟨by linarith, h0mem⟩)]
      rw [Nat.cast_one, Real.one_rpow]
      have hpow0 : (0:ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ (-σ + 1) :=
        Real.rpow_nonneg (by linarith) _
      have heq : (((N - 1 : ℕ) : ℝ) ^ (-σ + 1) - 1) / (-σ + 1)
          = (1 - ((N - 1 : ℕ) : ℝ) ^ (-σ + 1)) / (σ - 1) := by
        rw [show (-σ + 1) = -(σ - 1) by ring, div_neg, ← neg_div]
        congr 1
        ring
      rw [heq]
      gcongr
      linarith
    calc ∑ i ∈ Finset.Ico (0:ℕ) 2, 1 / (i : ℝ) ^ σ + ∑ i ∈ Finset.Ico (2:ℕ) N, 1 / (i : ℝ) ^ σ
        ≤ 1 + 1 / (σ - 1) := by
          rw [hhead]
          linarith [htail]
      _ = σ / (σ - 1) := by
          field_simp
          ring
section ConjSymmetry
open Finset Filter Metric Topology
end ConjSymmetry
section ZetaWindow
open Finset Filter Topology Metric
-- verbatim copies from SiegelTheorem.lean (telescope machinery)
end ZetaWindow
section TrivCharHeight
open Metric
end TrivCharHeight
section Quad341
open Metric
set_option maxHeartbeats 2000000
end Quad341
