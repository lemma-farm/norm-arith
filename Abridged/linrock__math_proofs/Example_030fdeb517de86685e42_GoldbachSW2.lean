module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_030fdeb517de86685e42_GoldbachSW2 ====
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
/-- **The E-Abel tail bound** (Siegel brick A2h-iv-b): with `|E(n)| ≤ C·n^{3/4}(1+log n)`,
    at real `β ∈ (9/10, 1)` the series tail beyond `x` is `≤ 400C·x^{7/8−β}` — the error
    that the choice `9/10 > 7/8` makes vanish. -/
theorem eabel_tail_bound (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) 
    (h_rpow_tail_sum_le : ∀ (p : ℝ),
      1 < p →
        ∀ (x : ℕ),
          1 ≤ x →
            ∀ (z : ℕ),
              x ≤ z → ∑ n ∈ Finset.Icc (x + 1) z, (↑n : ℝ) ^ (-p) ≤ (↑x : ℝ) ^ (1 - p) / (p - 1))
    (h_rpow_diff_le : ∀ (n : ℕ),
      1 ≤ n → ∀ (σ : ℝ), 0 ≤ σ → (↑n : ℝ) ^ (-σ) - (↑(n + 1) : ℝ) ^ (-σ) ≤ σ * (↑n : ℝ) ^ (-σ - 1))
    (h_eabel_term_real : ∀ (E : ℕ → ℝ) (n : ℕ) (β : ℝ),
      (↑(E n) : ℂ) * ((↑n : ℂ) ^ (-(↑β : ℂ)) - (↑(n + 1) : ℂ) ^ (-(↑β : ℂ))) =
        (↑(E n * ((↑n : ℝ) ^ (-β) - (↑(n + 1) : ℝ) ^ (-β))) : ℂ))
    :
    ‖(∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      - ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
    ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hβ0 : (0:ℝ) < β := by linarith
  have hp1 : (1:ℝ) < β + 1/8 := by linarith
  -- the pointwise majorant: ‖E(n)Δn‖ ≤ 9C·n^{−(β+1/8)} for n ≥ 1
  have hpoint : ∀ n : ℕ, 1 ≤ n →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [h_eabel_term_real, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := by
      have hmono : (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β) := by
        apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
        linarith
      linarith
    have hΔle : ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β - 1) := by
      calc ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)
          ≤ β * ((n:ℝ)) ^ (-β - 1) := h_rpow_diff_le n hn β hβ0.le
        _ ≤ 1 * ((n:ℝ)) ^ (-β - 1) := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            exact Real.rpow_nonneg hn0.le _
        _ = ((n:ℝ)) ^ (-β - 1) := one_mul _
    have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
      have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
        Real.log_le_rpow_div hn0.le (by norm_num)
      have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
      have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
        Real.one_le_rpow hn1r (by norm_num)
      linarith [h1, h2.le, h2.ge, h3]
    have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    have hEn := hE n hn
    have habs : |((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)|
        = ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := abs_of_nonneg hΔ0
    rw [habs]
    have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)
        = ((n:ℝ)) ^ (-(β + 1/8)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring
    calc |E n| * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
        ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (((n:ℝ)) ^ (-β - 1)) := by
          exact mul_le_mul hEn hΔle hΔ0 (by positivity)
      _ ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8)))) * (((n:ℝ)) ^ (-β - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)) := by
          ring
      _ = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by rw [hcollect]
  -- summability of the terms
  have hsummable : Summable (fun n : ℕ => ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr hp1)
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have heq : (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))
          = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n hn
  -- the finite sum is the range-x head (the n = 0 term vanishes)
  have hhead : ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = ∑ n ∈ range x, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) := by
    rw [show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    rw [hE0]
    simp
  rw [hhead]
  -- head/tail split of the tsum
  have hsplit : ∀ n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = (if n < x then ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
        + (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, add_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
  have hheadsum : Summable (fun n : ℕ => (if n < x then ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htailsum : Summable (fun n : ℕ => (if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖)
      hsummable.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have htsum_split : (∑' n : ℕ, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
        + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    calc ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
        = ∑' n : ℕ, ((if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
            + (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) :=
          hheadsum.tsum_add htailsum
      _ = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
          congr 1
          rw [tsum_eq_sum (s := range x) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  rw [htsum_split]
  rw [show ∀ (u v : ℂ), u + v - u = v from fun u v => by ring]
  -- bound the tail tsum by its norms
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hnormsum : Summable (fun n : ℕ => ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖) := htailsum.norm
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    intro z
    have hite : ∀ n ∈ range z, ‖if n < x then (0:ℂ) else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
        = (if x ≤ n then ‖((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 : ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) := hpoint x hx1
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8))
          = 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [Finset.mul_sum]
      have h4 := h_rpow_tail_sum_le (β + 1/8) hp1 x hx1 (z - 1) hm
      rw [show (1:ℝ) - (β + 1/8) = 7/8 - β by ring,
        show β + 1/8 - 1 = β - 7/8 by ring] at h4
      have hdenom : ((x:ℝ)) ^ (7/8 - β) / (β - 7/8) ≤ 40 * ((x:ℝ)) ^ (7/8 - β) := by
        rw [div_le_iff₀ (by linarith)]
        have h5 : (1:ℝ) ≤ 40 * (β - 7/8) := by linarith
        nlinarith [hxβ]
      have hxterm : ((x:ℝ)) ^ (-(β + 1/8)) ≤ ((x:ℝ)) ^ (7/8 - β) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1)
        linarith
      calc ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8))
            + 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
            have h6 : 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8))
                ≤ 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
              apply mul_le_mul_of_nonneg_left h4 (by positivity)
            linarith [le_trans h2 (le_of_eq h3), h1, h6,
              le_trans (le_trans h2 (le_of_eq h3)) h6]
        _ ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) + 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) := by
            have h7 : 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) :=
              mul_le_mul_of_nonneg_left hxterm (by positivity)
            have h8 : 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8))
                ≤ 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) :=
              mul_le_mul_of_nonneg_left hdenom (by positivity)
            linarith
        _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by nlinarith [hxβ, hC0]
  calc ‖∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))‖
      ≤ ∑' n : ℕ, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) :=
        hnormsum.tsum_le_of_sum_range_le hpartial

