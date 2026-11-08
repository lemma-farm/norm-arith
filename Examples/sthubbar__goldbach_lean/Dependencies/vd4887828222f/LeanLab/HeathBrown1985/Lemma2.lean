module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.vd4887828222f.LeanLab.HeathBrown1985.Elementary
/-!
P0096 Heath-Brown 1985, Lemma 2, 2.11, deduced from Lemma 1, 2.7, the bound 2.5 and the
divisor moments 2.2 with t = 2 and t = 3, following pages 50 to 52 of the paper.
The divisor moments are named inputs `DivMoment2` and `DivMoment3`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
def resSum (f : ℕ → ℝ) (N k r : ℕ) : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => n % k = r), f n
/-- Summing `F (l % k)` over `l ∈ [1, k]` is summing `F r` over `r < k`. -/
theorem sum_Icc_mod_eq (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∑ l ∈ Icc 1 k, F (l % k) = ∑ r ∈ range k, F r := by
  apply Finset.sum_nbij' (fun l => l % k) (fun r => if r = 0 then k else r)
  · intro l _; simp only [mem_range]; exact Nat.mod_lt _ (by omega)
  · intro r hr
    simp only [mem_range] at hr
    simp only [mem_Icc]
    split_ifs with h <;> omega
  · intro l hl
    simp only [mem_Icc] at hl
    split_ifs with h
    · rcases lt_or_eq_of_le hl.2 with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · exact h'.symm
    · rcases lt_or_eq_of_le hl.2 with h' | h'
      · exact Nat.mod_eq_of_lt h'
      · subst h'; simp at h
  · intro r hr
    simp only [mem_range] at hr
    split_ifs with h
    · subst h; simp
    · exact Nat.mod_eq_of_lt hr
  · intro l _; rfl
theorem delta1_eq (x : ℝ) (k : ℕ) (Q : ℝ) (hk : 1 ≤ k) :
    delta1 x k Q = ∑ r ∈ range k, |resSum (DeltaQ Q) ⌊x⌋₊ k r| := by
  unfold delta1 apSum
  exact sum_Icc_mod_eq k hk (fun r => |resSum (DeltaQ Q) ⌊x⌋₊ k r|)
theorem resSum_split (f : ℕ → ℝ) (N k j r : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    resSum f N k r =
      ∑ s ∈ (range (k * j)).filter (fun s => s % k = r), resSum f N (k * j) s := by
  unfold resSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Icc 1 N).filter (fun n => n % k = r))
    (t := (range (k * j)).filter (fun s => s % k = r)) (g := fun n => n % (k * j))]
  · apply sum_congr rfl
    intro s hs
    simp only [mem_filter, mem_range] at hs
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [← Nat.mod_mul_right_mod n k j, h3, hs.2]
  · intro n hn
    simp only [mem_filter] at hn
    simp only [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [Nat.mod_mul_right_mod, hn.2]
theorem delta1_le_mul (x : ℝ) (k j : ℕ) (Q : ℝ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    delta1 x k Q ≤ delta1 x (k * j) Q := by
  rw [delta1_eq x k Q hk, delta1_eq x (k * j) Q (Nat.one_le_iff_ne_zero.mpr (by positivity))]
  calc ∑ r ∈ range k, |resSum (DeltaQ Q) ⌊x⌋₊ k r|
      ≤ ∑ r ∈ range k, ∑ s ∈ (range (k * j)).filter (fun s => s % k = r),
          |resSum (DeltaQ Q) ⌊x⌋₊ (k * j) s| := by
        apply sum_le_sum; intro r _
        rw [resSum_split _ _ k j r hk hj]
        exact abs_sum_le_sum_abs _ _
    _ = _ := by
        apply Finset.sum_fiberwise_of_maps_to
        intro s _; simp only [mem_range]; exact Nat.mod_lt _ (by omega)
/-! ### Averaging over multiples, page 51 -/
theorem delta1_nonneg (x : ℝ) (k : ℕ) (Q : ℝ) : 0 ≤ delta1 x k Q :=
  sum_nonneg (fun _ _ => abs_nonneg _)
theorem avg_one (x Q : ℝ) (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    delta1 x k Q / k ≤ (2 / M) * ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
  set q := M / k with hq
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hkM
  have hlt : M < k * (q + 1) := by
    have := Nat.lt_mul_div_succ M (show 0 < k by omega); rw [hq]; linarith
  have hkq : k * q ≤ M := Nat.mul_div_le M k
  have h2 : M ≤ 2 * (k * q) := by nlinarith
  have hsub : (Icc 1 q).image (fun i => k * (q + i)) ⊆ (Ioc M (2 * M)).filter (k ∣ ·) := by
    intro h hh
    simp only [mem_image, mem_Icc] at hh
    obtain ⟨i, ⟨hi1, hiq⟩, rfl⟩ := hh
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · calc M < k * (q + 1) := hlt
        _ ≤ k * (q + i) := Nat.mul_le_mul_left _ (by omega)
    · calc k * (q + i) ≤ k * (q + q) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (k * q) := by ring
        _ ≤ 2 * M := by omega
  have hinj : Set.InjOn (fun i => k * (q + i)) (Icc 1 q : Set ℕ) := by
    intro a _ b _ hab
    have := Nat.eq_of_mul_eq_mul_left (show 0 < k by omega) hab
    omega
  have hsum : (q : ℝ) * delta1 x k Q ≤
      ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
    calc (q : ℝ) * delta1 x k Q = ∑ i ∈ Icc 1 q, delta1 x k Q := by
          rw [sum_const, nsmul_eq_mul]; simp
      _ ≤ ∑ i ∈ Icc 1 q, delta1 x (k * (q + i)) Q := by
          apply sum_le_sum; intro i hi
          exact delta1_le_mul x k (q + i) Q hk (by omega)
      _ = ∑ h ∈ (Icc 1 q).image (fun i => k * (q + i)), delta1 x h Q := by
          rw [sum_image hinj]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => delta1_nonneg _ _ _)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h2R : (M : ℝ) ≤ 2 * (k * q) := by exact_mod_cast h2
  have hd := delta1_nonneg x k Q
  rw [div_le_iff₀ hkR]
  calc delta1 x k Q = (2 / M) * (M / 2 * delta1 x k Q) := by field_simp
    _ ≤ (2 / M) * ((k * q) * delta1 x k Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hd; linarith
    _ ≤ (2 / M) * ((∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q) * k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = _ := by ring
theorem sum_avg (x Q : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, delta1 x k Q / k ≤
      (2 / M) * ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) * delta1 x h Q := by
  calc ∑ k ∈ Icc 1 M, delta1 x k Q / k
      ≤ ∑ k ∈ Icc 1 M, (2 / M) * ∑ h ∈ (Ioc M (2 * M)).filter (k ∣ ·), delta1 x h Q := by
        apply sum_le_sum; intro k hk
        exact avg_one x Q M k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    _ = (2 / M) * ∑ h ∈ Ioc M (2 * M), ∑ k ∈ (Icc 1 M).filter (· ∣ h), delta1 x h Q := by
        rw [← mul_sum]; congr 1
        rw [Finset.sum_comm' (t' := Ioc M (2 * M)) (s' := fun h => (Icc 1 M).filter (· ∣ h))]
        intro k h; simp only [mem_filter]; tauto
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum; intro h hh
        rw [sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (delta1_nonneg _ _ _)
        have hh0 : h ≠ 0 := by simp only [mem_Ioc] at hh; omega
        exact_mod_cast card_le_card (fun k hk => by
          simp only [mem_filter, mem_Icc] at hk
          exact Nat.mem_divisors.mpr ⟨hk.2, hh0⟩)
/-! ### Cauchy's inequality twice, 2.12 to 2.13 -/
/-- `δ₂` in residue form. -/
def delta2 (f : ℕ → ℝ) (N h : ℕ) : ℝ := ∑ r ∈ range h, (resSum f N h r) ^ 2
theorem delta1_sq_le (x : ℝ) (h : ℕ) (Q : ℝ) (hh : 1 ≤ h) :
    delta1 x h Q ^ 2 ≤ h * delta2 (DeltaQ Q) ⌊x⌋₊ h := by
  rw [delta1_eq x h Q hh]
  unfold delta2
  have := sq_sum_le_card_mul_sum_sq (s := range h) (f := fun r => |resSum (DeltaQ Q) ⌊x⌋₊ h r|)
  simpa [sq_abs] using this
theorem delta2_nonneg (f : ℕ → ℝ) (N h : ℕ) : 0 ≤ delta2 f N h :=
  sum_nonneg (fun _ _ => sq_nonneg _)
theorem cauchy_main (x Q : ℝ) (M : ℕ) (hM : 1 ≤ M) (W : ℝ)
    (hW : ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2 ≤ W) :
    (∑ k ∈ Icc 1 M, delta1 x k Q / k) ^ 2 ≤
      (4 / (M : ℝ) ^ 2) * W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set T := ∑ k ∈ Icc 1 M, delta1 x k Q / k
  set U := ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) * delta1 x h Q
  have hT0 : 0 ≤ T := sum_nonneg (fun k _ => div_nonneg (delta1_nonneg _ _ _) (by positivity))
  have hTU : T ≤ (2 / M) * U := sum_avg x Q M hM
  have hU2 : U ^ 2 ≤ (∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
      ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
  have hd1 : ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 ≤
      2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h := by
    rw [mul_sum]; apply sum_le_sum; intro h hh
    simp only [mem_Ioc] at hh
    refine (delta1_sq_le x h Q (by omega)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (delta2_nonneg _ _ _)
    exact_mod_cast hh.2
  have hS0 : 0 ≤ ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hW0 : 0 ≤ W := le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) hW
  calc T ^ 2 ≤ ((2 / M) * U) ^ 2 := pow_le_pow_left₀ hT0 hTU 2
    _ = (4 / (M : ℝ) ^ 2) * U ^ 2 := by ring
    _ ≤ (4 / (M : ℝ) ^ 2) * ((∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
          ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2) :=
        mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ ≤ (4 / (M : ℝ) ^ 2) * (W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hW hd1 hS0 hW0
    _ = _ := by ring
/-! ### Expanding `δ₂`, 2.14 -/
end LeanLab.HeathBrown1985
