module
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.U1493Theorem5Min
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.PrimePowerWindow.Count
/-!
# P0077 Halupczok 2012: Theorem 5 from Perelli-Pintz 1993, unit U-1496

AI wrote the Lean code, Claude, run 20261022T2003Z-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. (2) 47 (1993) 41-49, read from page images.

* `PP1993Thm3Printed`: PP1993 Theorem 3, p. 44, exactly as printed. It is the `2k`-TWIN
  PRIMES result, `n - m = 2k`, with `ψ*` and `P*` of p. 44. It is not a Goldbach statement.
* `PP1993Goldbach`: the Goldbach analogue of Theorem 3, with `R*` and `M*` of p. 43. It is not a
  numbered statement of PP1993. The paper establishes it in §§3-5: display (1) and (3), p. 44,
  reduce the mean square `∑_{N<2n≤N+H} |R*(2n) - M*(2n) 𝔖(2n)|²` to (4) and (5), and the
  paper proves (4) "for any `N^{7/12+ε} ≤ Y ≤ N`", §4 p. 45, and (5) "for any `Y ≥ Y₀(A,ε)` and
  `H ≥ Y^{1/3+ε}`", §5 p. 46, with `H = Y^{1/3+ε}` chosen on p. 44. Theorem 3 itself is
  derived on p. 44 by the sentence "the analogues of (4) and (5) ... imply the following
  theorem"; `PP1993Goldbach` is what (4) and (5) themselves give by the same sentence.
* `theorem5_of_PP : PP1993Goldbach → Theorem5`. CONDITIONAL ON `PP1993Goldbach` only.
  Elementary: the window condition `p₂ ∈ (X₂, X₂ + Y]` is the DIFFERENCE of two PP1993 sums,
  `R*(2k, 2X₁, 2X₁ - X₂) - R*(2k, 2X₁, 2X₁ - X₂ - Y)`, up to the `p₂` within `2R` of the two
  window ends, prime powers, and `M*` versus `Y`, all `≪ Y^{19/20}` per `k`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
open scoped ArithmeticFunction.vonMangoldt Classical
/-! ## Part 1. PP1993 as printed -/
/-- The summation condition of `R*(2n, N, Y)` and `M*(2n, N, Y)`, PP1993 p. 43, for `m = 2n`,
`h` the first prime and `k = m - h`: `N - Y < h ≤ N`, `k ≤ Y`. -/
def ppCond (m : ℕ) (N Y : ℝ) (h : ℕ) : Prop :=
  N - Y < (h : ℝ) ∧ (h : ℝ) ≤ N ∧ ((m - h : ℕ) : ℝ) ≤ Y
/-- PP1993 p. 43: `R*(2n, N, Y) = ∑_{h+k=2n, N-Y<h≤N, k≤Y} Λ(h) Λ(k)`, `h, k ≥ 1`, `m = 2n`. -/
noncomputable def ppR (m : ℕ) (N Y : ℝ) : ℝ :=
  ∑ h ∈ (Ioo 0 m).filter (ppCond m N Y), Λ h * Λ (m - h)
/-- PP1993 p. 43: `M*(2n, N, Y) = ∑_{h+k=2n, N-Y<h≤N, k≤Y} 1`. -/
noncomputable def ppM (m : ℕ) (N Y : ℝ) : ℝ :=
  (((Ioo 0 m).filter (ppCond m N Y)).card : ℝ)
theorem ppR_eq (m : ℕ) (N Y : ℝ) :
    ppR m N Y = ∑ h ∈ Ioo 0 m, (if ppCond m N Y h then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) := by
  rw [ppR, sum_filter]
  refine sum_congr rfl fun h _ => ?_
  split_ifs <;> simp
theorem ppM_eq (m : ℕ) (N Y : ℝ) :
    ppM m N Y = ∑ h ∈ Ioo 0 m, (if ppCond m N Y h then (1 : ℝ) else 0) := by
  rw [ppM, card_filter]; push_cast; rfl
/-- `binSum` as a sum over `h ∈ (0, m)` with the von Mangoldt weights. -/
theorem binSum_eq (X2 Y : ℝ) (m : ℕ) :
    binSum X2 Y m = ∑ h ∈ Ioo 0 m,
      (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) *
        (Λ h * Λ (m - h)) := by
  unfold binSum binSumAP
  rw [sum_filter]
  have hsub : Ioo 0 m ⊆ range (m + 1) := by
    intro h hh; rw [mem_Ioo] at hh; rw [mem_range]; omega
  rw [← sum_subset hsub ?_]
  · refine sum_congr rfl fun h hh => ?_
    by_cases c : (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime)
    · rw [if_pos c, one_mul, if_pos ⟨c.2.1, c.2.2, c.1.1, c.1.2, by simp [Int.modEq_one]⟩,
        ArithmeticFunction.vonMangoldt_apply_prime c.2.1,
        ArithmeticFunction.vonMangoldt_apply_prime c.2.2]
    · rw [if_neg c, zero_mul, if_neg]
      rintro ⟨a, b, d, e, -⟩
      exact c ⟨⟨d, e⟩, a, b⟩
  · intro h hh hn
    rw [if_neg]
    rintro ⟨a, b, -⟩
    apply hn
    rw [mem_Ioo]
    refine ⟨a.pos, ?_⟩
    have := b.pos
    omega
/-! ## Part 3. Indicator identities -/
/-- For `m = N + s`, `0 < s`, `X₂ + Y + s ≤ N`: the two PP1993 conditions differ exactly on
`X₂ + s ≤ h < X₂ + Y + s`. -/
theorem ind_diff {m h : ℕ} {N s X2 Y : ℝ} (hm : (m : ℝ) = N + s) (hhm : h < m) (hs : 0 < s)
    (hY : 0 ≤ Y) (hN : X2 + Y + s ≤ N) :
    (if ppCond m N (N - X2) h then (1 : ℝ) else 0) - (if ppCond m N (N - X2 - Y) h then 1 else 0)
      = if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then 1 else 0 := by
  have hmh : ((m - h : ℕ) : ℝ) = N + s - h := by rw [Nat.cast_sub hhm.le, hm]
  have e1 : ppCond m N (N - X2) h ↔ (X2 + s ≤ (h : ℝ) ∧ (h : ℝ) ≤ N) := by
    unfold ppCond; rw [hmh]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by linarith, b⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, b, by linarith⟩
  have e2 : ppCond m N (N - X2 - Y) h ↔ (X2 + Y + s ≤ (h : ℝ) ∧ (h : ℝ) ≤ N) := by
    unfold ppCond; rw [hmh]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by linarith, b⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, b, by linarith⟩
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  by_cases A : X2 + s ≤ (h : ℝ)
  · by_cases B : (h : ℝ) < X2 + Y + s
    · rw [if_pos ⟨A, by linarith⟩, if_neg (fun c => by linarith [c.1]), if_pos ⟨A, B⟩]; norm_num
    · rw [if_neg (fun c : _ ∧ _ => B c.2)]
      push_neg at B
      by_cases C : (h : ℝ) ≤ N
      · rw [if_pos ⟨A, C⟩, if_pos ⟨B, C⟩]; norm_num
      · rw [if_neg (fun c => C c.2), if_neg (fun c => C c.2)]; norm_num
  · rw [if_neg (fun c => A c.1), if_neg (fun c => by linarith [c.1]), if_neg (fun c => A c.1)]
    norm_num
/-- The pointwise error of the window difference against the prime window. -/
theorem coef_bound {h X2 Y s : ℝ} (P : Prop) [Decidable P] (hs : 0 < s) (hsY : s ≤ Y) :
    |(if X2 + s ≤ h ∧ h < X2 + Y + s then (1 : ℝ) else 0) -
        (if (X2 < h ∧ h ≤ X2 + Y) ∧ P then 1 else 0)| ≤
      (if X2 < h ∧ h < X2 + s then (1 : ℝ) else 0) +
        (if X2 + Y < h ∧ h < X2 + Y + s then 1 else 0) +
        (if (X2 < h ∧ h ≤ X2 + Y) ∧ ¬ P then 1 else 0) := by
  have n5 : (h < X2 + s) ↔ ¬ (X2 + s ≤ h) := not_le.symm
  have n6 : (X2 + Y < h) ↔ ¬ (h ≤ X2 + Y) := not_le.symm
  simp only [n5, n6]
  by_cases hp : P <;> by_cases a1 : X2 < h <;> by_cases a2 : h ≤ X2 + Y <;>
    by_cases a3 : X2 + s ≤ h <;> by_cases a4 : h < X2 + Y + s <;>
    simp only [hp, a1, a2, a3, a4, and_true, true_and, and_false, false_and, not_true,
      not_false_eq_true, if_true, if_false] <;> norm_num <;> linarith
/-! ## Part 4. Elementary bounds -/
theorem lam_le_log {n m : ℕ} (hn : n ≤ m) : Λ n ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [ArithmeticFunction.map_zero]; exact Real.log_natCast_nonneg m
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn))
theorem f_bound {m h : ℕ} (hh : h ≤ m) :
    0 ≤ Λ h * Λ (m - h) ∧ Λ h * Λ (m - h) ≤ Real.log m ^ 2 := by
  have a := lam_le_log hh
  have b := lam_le_log (Nat.sub_le m h)
  have a0 : 0 ≤ Λ h := ArithmeticFunction.vonMangoldt_nonneg
  have b0 : 0 ≤ Λ (m - h) := ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨mul_nonneg a0 b0, ?_⟩
  rw [sq]; exact mul_le_mul a b b0 (a0.trans a)
/-- Pairs with `h` in an open window of length `y`: at most `(y + 1) log² m`. -/
theorem window_sum_le (m : ℕ) {x y : ℝ} (hy : 0 ≤ y) :
    ∑ h ∈ Ioo 0 m, (if x < (h : ℝ) ∧ (h : ℝ) < x + y then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) ≤
      Real.log m ^ 2 * (y + 1) := by
  have hcard : ((((Ioo 0 m).filter (fun h : ℕ => x < (h : ℝ) ∧ (h : ℝ) < x + y)).card : ℕ) : ℝ)
      ≤ y / ((1 : ℕ) : ℝ) + 1 :=
    card_cong_le one_pos hy (fun h hh => by rw [mem_filter] at hh; exact ⟨hh.2.1, hh.2.2.le⟩)
      (fun _ _ _ _ => by simp [Int.modEq_one])
  calc _ ≤ ∑ h ∈ Ioo 0 m,
        (if x < (h : ℝ) ∧ (h : ℝ) < x + y then (1 : ℝ) else 0) * Real.log m ^ 2 := by
        refine sum_le_sum fun h hh => ?_
        have := f_bound (m := m) (h := h) (by rw [mem_Ioo] at hh; omega)
        split_ifs <;> simp [this.2]
    _ = Real.log m ^ 2 *
          ((((Ioo 0 m).filter (fun h : ℕ => x < (h : ℝ) ∧ (h : ℝ) < x + y)).card : ℕ) : ℝ) := by
        rw [← sum_mul, mul_comm, sum_boole]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa using hcard
/-- The von Mangoldt mass of the non-primes in `(0, m]`. -/
noncomputable def ppMass (m : ℕ) : ℝ := ∑ n ∈ (Ioc 0 m).filter (fun n => ¬ n.Prime), Λ n
theorem nonprime_sum_le (m : ℕ) (T : ℕ → Prop) [DecidablePred T] :
    ∑ h ∈ Ioo 0 m, (if T h ∧ ¬ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) *
        (Λ h * Λ (m - h)) ≤ 2 * Real.log m * ppMass m := by
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hpt : ∀ h ∈ Ioo 0 m,
      (if T h ∧ ¬ (h.Prime ∧ (m - h).Prime) then (1 : ℝ) else 0) * (Λ h * Λ (m - h)) ≤
        Real.log m * ((if ¬ h.Prime then Λ h else 0) +
          (if ¬ (m - h).Prime then Λ (m - h) else 0)) := by
    intro h hh
    rw [mem_Ioo] at hh
    have a := lam_le_log (n := h) (m := m) hh.2.le
    have b := lam_le_log (n := m - h) (m := m) (Nat.sub_le m h)
    have a0 : 0 ≤ Λ h := ArithmeticFunction.vonMangoldt_nonneg
    have b0 : 0 ≤ Λ (m - h) := ArithmeticFunction.vonMangoldt_nonneg
    have i1 : 0 ≤ (if ¬ h.Prime then Λ h else 0) := by split_ifs <;> simp [a0]
    have i2 : 0 ≤ (if ¬ (m - h).Prime then Λ (m - h) else 0) := by split_ifs <;> simp [b0]
    by_cases c : T h ∧ ¬ (h.Prime ∧ (m - h).Prime)
    · rw [if_pos c, one_mul]
      by_cases ph : h.Prime
      · have pm : ¬ (m - h).Prime := fun q => c.2 ⟨ph, q⟩
        rw [if_neg (not_not.mpr ph), if_pos pm, zero_add]
        exact mul_le_mul_of_nonneg_right a b0
      · rw [if_pos ph]
        calc Λ h * Λ (m - h) ≤ Λ h * Real.log m := mul_le_mul_of_nonneg_left b a0
          _ = Real.log m * Λ h := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hlog
    · rw [if_neg c, zero_mul]; positivity
  have hA : ∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) ≤ ppMass m := by
    rw [ppMass, sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro h hh; rw [mem_Ioo] at hh; rw [mem_Ioc]; omega
    · intro n _ _; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  have hB : ∑ h ∈ Ioo 0 m, (if ¬ (m - h).Prime then Λ (m - h) else 0) =
      ∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) := by
    apply sum_nbij' (fun h => m - h) (fun h => m - h)
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh ⊢; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh ⊢; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh; omega
    · intro h hh; simp only [mem_Ioo, coe_Ioo, Set.mem_Ioo] at hh; omega
    · intro h _; rfl
  calc _ ≤ ∑ h ∈ Ioo 0 m, Real.log m * ((if ¬ h.Prime then Λ h else 0) +
          (if ¬ (m - h).Prime then Λ (m - h) else 0)) := sum_le_sum hpt
    _ = Real.log m * (∑ h ∈ Ioo 0 m, (if ¬ h.Prime then Λ h else 0) +
          ∑ h ∈ Ioo 0 m, (if ¬ (m - h).Prime then Λ (m - h) else 0)) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ Real.log m * (ppMass m + ppMass m) := by
        rw [hB]; exact mul_le_mul_of_nonneg_left (by linarith) hlog
    _ = 2 * Real.log m * ppMass m := by ring
theorem natLog_le (m : ℕ) (hm : 1 ≤ m) : ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log m := by
  have h1 : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 m : ℕ) : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := Real.log_two_gt_d9
  have h4 : 0 ≤ ((Nat.log 2 m : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith
/-- The prime power mass: `ppMass m ≤ 4 log² m · m^{1/2}`. -/
theorem ppMass_le {m : ℕ} (hm : 1 ≤ m) :
    ppMass m ≤ 4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by
  have h1 := LeanLab.PrimePowerWindow.sum_nonprime_le 0 m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hm' (by norm_num)
  have hterm : ∀ k ∈ Icc 2 (Nat.log 2 m), (Real.log m / k) *
      ((((Iic m).filter (fun j => 0 < j ^ k ∧ j ^ k ≤ m)).card : ℕ) : ℝ) ≤
        Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ)) := by
    intro k hk
    rw [mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hc := LeanLab.PrimePowerWindow.count_le (a := 0) (b := (m : ℝ)) le_rfl
      (Nat.cast_nonneg m) hk1
    rw [Nat.floor_natCast, Nat.floor_zero] at hc
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hz : (0 : ℝ) ^ (1 / (k : ℝ)) = 0 := Real.zero_rpow (by positivity)
    rw [hz, sub_zero] at hc
    have hr : (m : ℝ) ^ (1 / (k : ℝ)) ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm'
        (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk.1))
    have hdiv : Real.log m / k ≤ Real.log m := div_le_self hlog (by exact_mod_cast hk1)
    have hdiv0 : 0 ≤ Real.log m / k := div_nonneg hlog hkpos.le
    calc _ ≤ Real.log m * ((m : ℝ) ^ (1 / 2 : ℝ) + 1) :=
          mul_le_mul hdiv (by linarith) (Nat.cast_nonneg _) hlog
      _ ≤ _ := by nlinarith
  have hcardI : ((Icc 2 (Nat.log 2 m)).card : ℝ) ≤ 2 * Real.log m := by
    rw [Nat.card_Icc]
    refine le_trans ?_ (natLog_le m hm)
    exact_mod_cast (by omega : Nat.log 2 m + 1 - 2 ≤ Nat.log 2 m)
  calc ppMass m ≤ _ := h1
    _ ≤ ∑ k ∈ Icc 2 (Nat.log 2 m), Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ)) := sum_le_sum hterm
    _ = ((Icc 2 (Nat.log 2 m)).card : ℝ) * (Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.log m) * (Real.log m * (2 * (m : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardI (by positivity)
    _ = 4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring
/-- Integers in `[a, b)`, `b = a + Y`, inside `(0, m)`: their number is within `1` of `Y`. -/
theorem card_window {m : ℕ} {a b Y : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) (hb : b = a + Y)
    (ham : b < m) :
    |∑ h ∈ Ioo 0 m, (if a ≤ (h : ℝ) ∧ (h : ℝ) < b then (1 : ℝ) else 0) - Y| ≤ 1 := by
  subst hb
  have hset : (Ioo 0 m).filter (fun h : ℕ => a ≤ (h : ℝ) ∧ (h : ℝ) < a + Y) =
      Ico ⌈a⌉₊ ⌈a + Y⌉₊ := by
    ext h
    simp only [mem_filter, mem_Ioo, mem_Ico, Nat.ceil_le, Nat.lt_ceil]
    constructor
    · rintro ⟨-, b, c⟩; exact ⟨b, c⟩
    · rintro ⟨b, c⟩
      refine ⟨⟨?_, ?_⟩, b, c⟩
      · exact_mod_cast (show (0 : ℝ) < h by linarith)
      · exact_mod_cast (show (h : ℝ) < m by linarith)
  rw [sum_boole, hset, Nat.card_Ico, Nat.cast_sub (Nat.ceil_mono (by linarith))]
  have h1 := Nat.le_ceil (a + Y)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ a + Y by linarith)
  have h3 := Nat.le_ceil a
  have h4 := Nat.ceil_lt_add_one ha.le
  rw [abs_le]; constructor <;> linarith
/-! ### The singular series is at most `2^17 r^{1/4}` -/
theorem f2_mem {p : ℕ} (hp : p.Prime) : 0 ≤ f2 p ∧ f2 p ≤ 1 := by
  unfold f2
  split_ifs with h2
  · norm_num
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      exact_mod_cast (show 3 ≤ p by omega)
    have hq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hq0 : 0 < ((p : ℝ) - 1) ^ 2 := by linarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    constructor <;> linarith
theorem twinC_mem : 0 ≤ twinC ∧ twinC ≤ 1 := by
  constructor
  · exact ge_of_tendsto' twinC_tendsto fun w =>
      prod_nonneg fun p hp => (f2_mem (prime_of_mem_PrN hp)).1
  · exact le_of_tendsto' twinC_tendsto fun w =>
      prod_le_one₀ (fun p hp => (f2_mem (prime_of_mem_PrN hp)).1)
        (fun p hp => (f2_mem (prime_of_mem_PrN hp)).2)
theorem sixteen_rpow : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num
theorem factor_le {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) ∧
      ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ (if p < 16 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 4 : ℝ) := by
  have h3 : (3 : ℝ) ≤ p := by
    have := hp.two_le
    exact_mod_cast (show 3 ≤ p by omega)
  have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hle2 : ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
  split_ifs with h16
  · nlinarith
  · push_neg at h16
    have : (16 : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast h16) (by norm_num)
    rw [sixteen_rpow] at this
    linarith
theorem S_abs_le {r : ℕ} (hr : 1 ≤ r) : |S r| ≤ 2 ^ 17 * (r : ℝ) ^ (1 / 4 : ℝ) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := by positivity
  set F := r.primeFactors.filter (· ≠ 2) with hF
  have hFp : ∀ p ∈ F, p.Prime ∧ p ≠ 2 := by
    intro p hp; rw [hF, mem_filter, Nat.mem_primeFactors] at hp; exact ⟨hp.1.1, hp.2⟩
  have hprod0 : 0 ≤ ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) :=
    prod_nonneg fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).1
  have hc : ∏ p ∈ F, (if p < 16 then (2 : ℝ) else 1) ≤ 2 ^ 16 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    apply pow_le_pow_right₀ (by norm_num)
    calc (F.filter (· < 16)).card ≤ (range 16).card := by
          apply card_le_card; intro p hp; rw [mem_filter] at hp; rw [mem_range]; exact hp.2
      _ = 16 := card_range 16
  have hP : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ r := by
    have h1 : ∏ p ∈ F, p ≤ ∏ p ∈ r.primeFactors, p :=
      prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
        (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    have h2 : ∏ p ∈ r.primeFactors, p ≤ r := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd r)
    exact_mod_cast h1.trans h2
  have hprod : ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ) := by
    calc ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ ∏ p ∈ F, ((if p < 16 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 4 : ℝ)) :=
          prod_le_prod₀ (fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).1)
            (fun p hp => (factor_le (hFp p hp).1 (hFp p hp).2).2)
      _ = (∏ p ∈ F, (if p < 16 then (2 : ℝ) else 1)) * (∏ p ∈ F, (p : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      _ ≤ 2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ) := by
          apply mul_le_mul hc _ (by positivity) (by norm_num)
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          have hP' := hP
          push_cast at hP'
          exact hP'
  obtain ⟨t0, t1⟩ := twinC_mem
  unfold S
  rw [← hF]
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    calc 2 * twinC * ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ 2 * 1 * (2 ^ 16 * (r : ℝ) ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul (by linarith) hprod hprod0 (by norm_num)
      _ = 2 ^ 17 * (r : ℝ) ^ (1 / 4 : ℝ) := by ring
  · rw [abs_zero]; positivity
/-! ## Part 5. The pointwise decomposition -/
theorem mem_kRange' {X R : ℝ} {k : ℕ} (hk : k ∈ kRange X R) : X < k ∧ (k : ℝ) ≤ X + R := by
  unfold kRange at hk; rw [mem_filter] at hk; exact hk.2
theorem kRange_mono {X R R' : ℝ} (h : R ≤ R') : kRange X R ⊆ kRange X R' := by
  intro k hk
  unfold kRange at hk ⊢
  rw [mem_filter] at hk ⊢
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨?_, h2, by linarith⟩
  rw [mem_Icc] at h1 ⊢
  exact ⟨h1.1, h1.2.trans (Nat.ceil_mono (by linarith))⟩
theorem card_kRange_le {X R : ℝ} (hR : 0 ≤ R) : ((kRange X R).card : ℝ) ≤ R + 1 := by
  have := card_cong_le (S := kRange X R) (l := 1) one_pos hR (fun k hk => mem_kRange' hk)
    (fun _ _ _ _ => by simp [Int.modEq_one])
  simpa using this
/-- **Pointwise.** For `m = 2k`, `X₁ < k ≤ X₁ + R`, `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y`: the
Halupczok error at `2k` minus the difference of the two PP1993 errors at
`N = 2X₁`, `Y' = 2X₁ - X₂` and `Y' = 2X₁ - X₂ - Y` is at most
`2(2R+1) log² m + 8 log³ m · m^{1/2} + 2^17 m^{1/4}`. -/
theorem pointwise {X1 X2 Y R : ℝ} {k : ℕ} (hk : k ∈ kRange X1 R) (hY : 0 < Y) (hX2 : 0 ≤ X2)
    (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y) :
    |(binSum X2 Y (2 * k) - S (2 * k) * Y) -
        ((ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) -
          (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
            S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)))| ≤
      2 * (2 * R + 1) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 +
        8 * Real.log ((2 * k : ℕ) : ℝ) ^ 3 * ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) +
        2 ^ 17 * ((2 * k : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨hk1, hk2⟩ := mem_kRange' hk
  set m := 2 * k with hmdef
  set N := 2 * X1 with hN
  set s := (m : ℝ) - N with hs
  have hmR : (m : ℝ) = N + s := by rw [hs]; ring
  have hmk : (m : ℝ) = 2 * k := by rw [hmdef]; push_cast; ring
  have hs0 : 0 < s := by rw [hs, hmk, hN]; linarith
  have hs2 : s ≤ 2 * R := by rw [hs, hmk, hN]; linarith
  have hsY : s ≤ Y := by linarith
  have hNs : X2 + Y + s ≤ N := by rw [hN]; linarith
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := by linarith
    have : 0 < m := by exact_mod_cast this
    omega
  set f : ℕ → ℝ := fun h => Λ h * Λ (m - h) with hf
  -- the window identity
  have hdiffR : ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m =
      ∑ h ∈ Ioo 0 m, ((if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) -
        (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then 1 else 0)) *
          f h := by
    rw [ppR_eq, ppR_eq, binSum_eq, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [mem_Ioo] at hh
    rw [← ind_diff hmR hh.2 hs0 hY.le hNs]
    simp only [hf]; ring
  have hdiffM : ppM m N (N - X2) - ppM m N (N - X2 - Y) =
      ∑ h ∈ Ioo 0 m, (if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) := by
    rw [ppM_eq, ppM_eq, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [mem_Ioo] at hh
    exact ind_diff hmR hh.2 hs0 hY.le hNs
  -- bound of the window identity
  have hlog0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hR1 : |ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m| ≤
      2 * (2 * R + 1) * Real.log m ^ 2 + 8 * Real.log m ^ 3 * (m : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hdiffR]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ h ∈ Ioo 0 m,
        |((if X2 + s ≤ (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then (1 : ℝ) else 0) -
          (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ (h.Prime ∧ (m - h).Prime) then 1 else 0)) *
            f h| ≤
        (if X2 < (h : ℝ) ∧ (h : ℝ) < X2 + s then (1 : ℝ) else 0) * f h +
          (if X2 + Y < (h : ℝ) ∧ (h : ℝ) < X2 + Y + s then 1 else 0) * f h +
          (if (X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y) ∧ ¬ (h.Prime ∧ (m - h).Prime) then 1 else 0) *
            f h := by
      intro h hh
      rw [mem_Ioo] at hh
      have hf0 : 0 ≤ f h := (f_bound (m := m) (h := h) hh.2.le).1
      rw [abs_mul, abs_of_nonneg hf0, ← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right (coef_bound _ hs0 hsY) hf0
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, sum_add_distrib]
    have e1 := window_sum_le m (x := X2) hs0.le
    have e2 := window_sum_le m (x := X2 + Y) hs0.le
    have e3 := nonprime_sum_le m (fun h => X2 < (h : ℝ) ∧ (h : ℝ) ≤ X2 + Y)
    have e4 := ppMass_le hm1
    simp only [hf] at e1 e2 e3 ⊢
    have : 2 * Real.log m * ppMass m ≤
        2 * Real.log m * (4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left e4 (by positivity)
    have hl2 : 0 ≤ Real.log m ^ 2 := sq_nonneg _
    have hs1 : Real.log m ^ 2 * (s + 1) ≤ Real.log m ^ 2 * (2 * R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hl2
    have e5 : 2 * Real.log m * (4 * Real.log m ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ)) =
        8 * Real.log m ^ 3 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring
    linarith
  have hM1 : |ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y| ≤ 1 := by
    rw [hdiffM]
    apply card_window (a := X2 + s) (by linarith) hY.le (by ring)
    rw [hmR]; linarith
  have hS := S_abs_le hm1
  have key : (binSum X2 Y m - S m * Y) -
      ((ppR m N (N - X2) - S m * ppM m N (N - X2)) -
        (ppR m N (N - X2 - Y) - S m * ppM m N (N - X2 - Y))) =
      -(ppR m N (N - X2) - ppR m N (N - X2 - Y) - binSum X2 Y m) +
        S m * (ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul]
  have hSM : |S m| * |ppM m N (N - X2) - ppM m N (N - X2 - Y) - Y| ≤
      2 ^ 17 * (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc _ ≤ |S m| * 1 := mul_le_mul_of_nonneg_left hM1 (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hS
  linarith
/-! ## Part 6. The core sum over one window -/
/-- The error bound `Emax` at the top `M = 2X₁ + 2R` of the window. -/
noncomputable def Emax (R M : ℝ) : ℝ :=
  2 * (2 * R + 1) * Real.log M ^ 2 + 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ) +
    2 ^ 17 * M ^ (1 / 4 : ℝ)
theorem sq_three (a b c : ℝ) : (a - b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b + c)]
/-- **Core.** One window `X₁ < k ≤ X₁ + R` with `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y` and `R` at most half
of both PP1993 window lengths `(2X₁ - X₂)^a` and `(2X₁ - X₂ - Y)^a`: the Halupczok mean square is
at most three times the two PP1993 mean squares plus `3 (R + 1) Emax²`. -/
theorem core_sum {X1 X2 Y R a Bhi Blo : ℝ}
    (hhi : ∑ k ∈ kRange X1 ((2 * X1 - X2) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) ^ 2
        ≤ Bhi)
    (hlo : ∑ k ∈ kRange X1 ((2 * X1 - X2 - Y) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
        S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)) ^ 2 ≤ Blo)
    (hY : 0 < Y) (hX2 : 0 ≤ X2) (hR : 0 ≤ R) (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y)
    (hRhi : R ≤ (2 * X1 - X2) ^ a / 2) (hRlo : R ≤ (2 * X1 - X2 - Y) ^ a / 2) :
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      3 * Bhi + 3 * Blo + 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 := by
  set M := 2 * X1 + 2 * R with hM
  set Dhi : ℕ → ℝ := fun k =>
    ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2) with hDhi
  set Dlo : ℕ → ℝ := fun k => ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
    S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y) with hDlo
  have hE0 : ∀ k ∈ kRange X1 R, |(binSum X2 Y (2 * k) - S (2 * k) * Y) - (Dhi k - Dlo k)| ≤
      Emax R M := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_kRange' hk
    have hp := pointwise hk hY hX2 h2R hV
    have hk0 : (0 : ℝ) < k := by linarith
    have hk1' : 1 ≤ k := by
      have : 0 < k := by exact_mod_cast hk0
      omega
    have hm1 : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1'
      push_cast; linarith
    have hmM : ((2 * k : ℕ) : ℝ) ≤ M := by push_cast; rw [hM]; linarith
    have hl : Real.log ((2 * k : ℕ) : ℝ) ≤ Real.log M := Real.log_le_log (by linarith) hmM
    have hl0 : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg hm1
    have h12 : ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hmM (by norm_num)
    have h14 : ((2 * k : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ M ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hmM (by norm_num)
    have hsq0 : 0 ≤ ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hl2 : Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤ Real.log M ^ 2 := pow_le_pow_left₀ hl0 hl 2
    have hl3 : Real.log ((2 * k : ℕ) : ℝ) ^ 3 ≤ Real.log M ^ 3 := pow_le_pow_left₀ hl0 hl 3
    have t1 : 2 * (2 * R + 1) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤
        2 * (2 * R + 1) * Real.log M ^ 2 := mul_le_mul_of_nonneg_left hl2 (by linarith)
    have t2 : Real.log ((2 * k : ℕ) : ℝ) ^ 3 * ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤
        Real.log M ^ 3 * M ^ (1 / 2 : ℝ) :=
      mul_le_mul hl3 h12 hsq0 (by have := Real.log_nonneg (show (1 : ℝ) ≤ M by linarith); positivity)
    unfold Emax
    simp only [hDhi, hDlo]
    linarith
  have hpt : ∀ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      3 * Dhi k ^ 2 + 3 * Dlo k ^ 2 + 3 * Emax R M ^ 2 := by
    intro k hk
    have h := hE0 k hk
    set e := (binSum X2 Y (2 * k) - S (2 * k) * Y) - (Dhi k - Dlo k) with he
    have : binSum X2 Y (2 * k) - S (2 * k) * Y = Dhi k - Dlo k + e := by rw [he]; ring
    rw [this]
    have h3 := sq_three (Dhi k) (Dlo k) e
    have : e ^ 2 ≤ Emax R M ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    linarith
  have hsubhi : ∑ k ∈ kRange X1 R, Dhi k ^ 2 ≤ Bhi :=
    (sum_le_sum_of_subset_of_nonneg (kRange_mono hRhi) (fun _ _ _ => sq_nonneg _)).trans hhi
  have hsublo : ∑ k ∈ kRange X1 R, Dlo k ^ 2 ≤ Blo :=
    (sum_le_sum_of_subset_of_nonneg (kRange_mono hRlo) (fun _ _ _ => sq_nonneg _)).trans hlo
  have hcard := card_kRange_le (X := X1) hR
  calc _ ≤ ∑ k ∈ kRange X1 R, (3 * Dhi k ^ 2 + 3 * Dlo k ^ 2 + 3 * Emax R M ^ 2) := sum_le_sum hpt
    _ = 3 * ∑ k ∈ kRange X1 R, Dhi k ^ 2 + 3 * ∑ k ∈ kRange X1 R, Dlo k ^ 2 +
          ((kRange X1 R).card : ℝ) * (3 * Emax R M ^ 2) := by
        rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum, mul_sum]
    _ ≤ 3 * Bhi + 3 * Blo + (R + 1) * (3 * Emax R M ^ 2) := by
        have : 0 ≤ 3 * Emax R M ^ 2 := by positivity
        nlinarith
    _ = _ := by ring
/-! ## Part 7. Asymptotics on one window of the minimal scale -/
end LeanLab.Halupczok2012
