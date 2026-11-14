module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_f44930f6811d8b56f040_GoldbachSW2 ====
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


set_option linter.unusedVariables false in
/-- **THE ζ-TRUNCATION BOUND** (Siegel brick A2h-ii-ε): at real `β′ ∈ (9/10, 1)`,
    `‖(β′−1)(ζ(β′) − Σ_{n<x}n^{−β′}) − x^{1−β′}‖ ≤ 11·x^{−β′}` for `x ≥ 2` — the
    quantitative form the Goldfeld master inequality consumes. -/
theorem zeta_truncation (x : ℕ) (hx : 2 ≤ x) {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) 
    (h_euler_maclaurin_kernel : ∀ (s : ℂ) (n : ℕ),
      2 ≤ n →
        ∀ (W : ℝ),
          ‖1 - s‖ ≤ W →
            W * (1 / (↑n : ℝ)) ≤ 1 →
              ‖(s - 1) * (↑n : ℂ) ^ (-s) - ((↑n : ℂ) ^ (1 - s) - (↑(n + 1) : ℂ) ^ (1 - s))‖ ≤
                4 * (W + 1) ^ 2 * (1 / (↑n : ℝ)) ^ 2 * (↑n : ℝ) ^ (1 - s.re))
    (h_zeta_truncation_identity : ∀ (x : ℕ),
      1 ≤ x →
        ∀ {β : ℝ},
          9 / 10 < β →
            β < 1 →
              (∑' (n : ℕ),
                  if n < x then 0
                  else
                    ((↑β : ℂ) - 1) * (↑n : ℂ) ^ (-(↑β : ℂ)) -
                      ((↑n : ℂ) ^ (1 - (↑β : ℂ)) - (↑(n + 1) : ℂ) ^ (1 - (↑β : ℂ)))) =
                ((↑β : ℂ) - 1) * (riemannZeta (↑β : ℂ) - ∑ n ∈ Finset.range x, (↑n : ℂ) ^ (-(↑β : ℂ))) -
                  (↑x : ℂ) ^ (1 - (↑β : ℂ)))
    (h_rpow_tail_sum_le : ∀ (p : ℝ),
      1 < p →
        ∀ (x : ℕ),
          1 ≤ x →
            ∀ (z : ℕ),
              x ≤ z → ∑ n ∈ Finset.Icc (x + 1) z, (↑n : ℝ) ^ (-p) ≤ (↑x : ℝ) ^ (1 - p) / (p - 1))
    :
    ‖(((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ ≤ 11 * ((x:ℝ)) ^ (-β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  rw [← h_zeta_truncation_identity x hx1 hβ1 hβ2]
  -- the pointwise kernel bound at s = β′
  have hpoint : ∀ n : ℕ, x ≤ n →
      ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
      ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hx hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hW : ‖1 - ((β:ℂ))‖ ≤ 1/10 := by
      rw [show (1:ℂ) - ((β:ℂ)) = (((1 - β : ℝ)):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hWn : (1/10 : ℝ) * (1 / (n:ℝ)) ≤ 1 := by
      have h1 : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        linarith
      linarith
    have hker := h_euler_maclaurin_kernel ((β:ℂ)) n hn2 (1/10) hW hWn
    rw [Complex.ofReal_re] at hker
    have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) = ((n:ℝ)) ^ (-(1 + β)) := by
      have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
        rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
          ← Real.rpow_neg hn0.le]
      rw [hpow2, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
    calc ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
        ≤ 4 * (1/10 + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) := hker
      _ = 4 * (1/10 + 1) ^ 2 * (((n:ℝ)) ^ (-(1 + β))) := by
          rw [← hcollect]
          ring
      _ ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
          have ht : (0:ℝ) ≤ ((n:ℝ)) ^ (-(1 + β)) := Real.rpow_nonneg hn0.le _
          nlinarith [ht]
  -- partial sums of the norms are uniformly ≤ 11 x^{−β}
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z,
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
      ≤ 11 * ((x:ℝ)) ^ (-β) := by
    intro z
    have hite : ∀ n ∈ range z,
        ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
        = (if x ≤ n then ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖ else 0) := by
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
      have h1 := hpoint x (le_refl x)
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1),
          ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
            - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β))
          = 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β)) := by
        rw [Finset.mul_sum]
      have h4 := h_rpow_tail_sum_le (1 + β) (by linarith) x hx1 (z - 1) hm
      rw [show (1:ℝ) - (1 + β) = -β by ring, show (1:ℝ) + β - 1 = β by ring] at h4
      -- x-term: 5x^{−(1+β)} ≤ (5/2)x^{−β}
      have hxsplit : ((x:ℝ)) ^ (-(1 + β)) = ((x:ℝ)) ^ (-β) * ((x:ℝ)) ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hxinv : ((x:ℝ)) ^ (-(1:ℝ)) ≤ 1/2 := by
        rw [Real.rpow_neg_one, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hx
      have h5 : 5 * ((x:ℝ)) ^ (-(1 + β)) ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) := by
        rw [hxsplit]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hxinv hxβ
      -- tail: 5·x^{−β}/β ≤ 5·x^{−β}·(10/9)
      have hβinv : (1:ℝ)/β ≤ 10/9 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h6 : ((x:ℝ)) ^ (-β) / β ≤ ((x:ℝ)) ^ (-β) * (10/9) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hβinv hxβ
      calc ‖(((β:ℂ)) - 1) * ((x:ℂ)) ^ (-(β:ℂ))
            - (((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1),
              ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
                - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ 5 * ((x:ℝ)) ^ (-(1 + β))
            + 5 * (((x:ℝ)) ^ (-β) / β) := by
            have := le_trans h2 (le_of_eq h3)
            have h7 : 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β))
                ≤ 5 * (((x:ℝ)) ^ (-β) / β) := by
              apply mul_le_mul_of_nonneg_left h4 (by norm_num)
            linarith
        _ ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) + 5 * (((x:ℝ)) ^ (-β) * (10/9)) := by
            have h8 : 5 * (((x:ℝ)) ^ (-β) / β) ≤ 5 * (((x:ℝ)) ^ (-β) * (10/9)) :=
              mul_le_mul_of_nonneg_left h6 (by norm_num)
            linarith
        _ ≤ 11 * ((x:ℝ)) ^ (-β) := by linarith
  -- summability of the norms
  have hnorm_sum : Summable (fun n : ℕ =>
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖) := by
    have hmaj : Summable (fun n : ℕ => (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hmaj
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg (not_lt.mpr h)]
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this
      have heq : (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β)) = 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n h
  -- assemble
  calc ‖∑' n : ℕ, (if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))‖
      ≤ ∑' n : ℕ, ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ 11 * ((x:ℝ)) ^ (-β) :=
        hnorm_sum.tsum_le_of_sum_range_le hpartial
