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
section ConjSymmetry
open Finset Filter Metric Topology
end ConjSymmetry
section ZetaWindow
open Finset Filter Topology Metric
-- verbatim copies from SiegelTheorem.lean (telescope machinery)
lemma tsum_cpow_telescope (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  -- partial sums telescope
  have hpartial : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- the real telescoping majorant
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  -- majorant partial sums telescope
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- summability from the kernel bound at s − 1
  have hsummable : Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
      else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
        - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
    · -- majorant summable: nonneg terms with telescoping bounded partials
      apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
      · intro n
        rcases Nat.lt_or_ge n x with h | h
        · rw [if_pos h]
        · rw [if_neg (by omega)]
          apply mul_nonneg hC0
          have := hgmono n (le_trans hx h)
          linarith
      · intro z
        rcases Nat.lt_or_ge z x with hz | hz
        · -- every index n < z ≤ x: all terms vanish
          have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
              else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
                - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_pos (by omega)]
          rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
          exact hC0
        · rw [hpartialR z hz]
          have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
            apply Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast hx)
            linarith
          have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
            Real.rpow_nonneg (Nat.cast_nonneg z) _
          calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
              ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
                apply mul_le_mul_of_nonneg_left _ hC0
                linarith
            _ = ‖s - 1‖ / (s.re - 1) := mul_one _
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, norm_zero]
      · rw [if_neg (by omega), if_neg (by omega)]
        have hn1 : 1 ≤ n := le_trans hx h
        have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
          simp only [Complex.sub_re, Complex.one_re]
          linarith)
        have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        rw [he1, he2]
        have hre : (s - 1).re = s.re - 1 := by
          simp [Complex.sub_re]
        rw [hre] at hker
        exact hker
  -- conclude: tsum = limit of partials = x^{1−s}
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) := by
    have hz0 : Tendsto (fun z : ℕ => ((z:ℂ)) ^ ((1:ℂ) - s)) atTop (nhds 0) := by
      have h1s : ((1:ℂ) - s) ≠ 0 := by
        intro hc
        have := congrArg Complex.re hc
        simp at this
        linarith
      have hbnd : ∀ z : ℕ, ‖((z:ℂ)) ^ ((1:ℂ) - s)‖ ≤ ((z:ℝ)) ^ (1 - s.re) := by
        intro z
        rcases Nat.eq_zero_or_pos z with rfl | hzpos
        · simp only [Nat.cast_zero]
          rw [Complex.zero_cpow h1s, norm_zero,
            Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0)]
        · rw [Complex.norm_natCast_cpow_of_pos hzpos]
          have hre1 : ((1:ℂ) - s).re = 1 - s.re := by simp [Complex.sub_re]
          rw [hre1]
      have hg0 : Tendsto (fun z : ℕ => ((z:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have h := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := h.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      exact squeeze_zero_norm hbnd hg0
    have := (tendsto_const_nhds (x := ((x:ℂ)) ^ ((1:ℂ) - s))).sub hz0
    simpa using this
  have heq : (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      =ᶠ[atTop] (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s)) := by
    filter_upwards [eventually_ge_atTop x] with z hz
    exact hpartial z hz
  have hrange' : Tendsto (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) :=
    (Filter.tendsto_congr' heq).mpr hlim
  exact tendsto_nhds_unique hrange hrange'
lemma tsum_cpow_telescope_summable (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
    else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
      - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
  · apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h]
      · rw [if_neg (by omega)]
        apply mul_nonneg hC0
        have := hgmono n (le_trans hx h)
        linarith
    · intro z
      rcases Nat.lt_or_ge z x with hz | hz
      · have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos (by omega)]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
        exact hC0
      · rw [hpartialR z hz]
        have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast hx)
          linarith
        have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
          Real.rpow_nonneg (Nat.cast_nonneg z) _
        calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
            ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
              apply mul_le_mul_of_nonneg_left _ hC0
              linarith
          _ = ‖s - 1‖ / (s.re - 1) := mul_one _
  · intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (by omega), if_neg (by omega)]
      have hn1 : 1 ≤ n := le_trans hx h
      have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith)
      have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      rw [he1, he2]
      have hre : (s - 1).re = s.re - 1 := by
        simp [Complex.sub_re]
      rw [hre] at hker
      exact hker
end ZetaWindow
section TrivCharHeight
open Metric
end TrivCharHeight
section Quad341
open Metric
set_option maxHeartbeats 2000000
end Quad341
