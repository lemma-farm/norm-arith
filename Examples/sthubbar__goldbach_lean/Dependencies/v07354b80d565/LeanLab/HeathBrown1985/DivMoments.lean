module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.HeathBrown1985.Lemma2
/-!
P0096 Heath-Brown 1985, the cases t = 2 and t = 3 of 2.2:
`Σ_{n ≤ N} d(n)² ≤ N (1 + log N)³` and `Σ_{n ≤ N} d(n)³ ≤ N (1 + log N)⁷`, elementary,
by `d(n)² = #{(x, y) : x ∣ n, y ∣ n}` and `1/[x, y] = (x, y)/(xy)`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
attribute [local instance] Classical.propDecidable
/-- `H_N = Σ_{j ≤ N} 1/j`. -/
def Hn (N : ℕ) : ℝ := ∑ j ∈ Icc 1 N, (j : ℝ)⁻¹
theorem Hn_nonneg (N : ℕ) : 0 ≤ Hn N := sum_nonneg (fun _ _ => by positivity)
theorem Hn_le (N : ℕ) : Hn N ≤ 1 + Real.log N := sum_inv_Icc_le_log N
/-- Multiples of `g` up to `N`, weighted by `1/x`. -/
theorem sum_inv_multiples_le (N g : ℕ) (hg : 1 ≤ g) :
    ∑ x ∈ (Icc 1 N).filter (g ∣ ·), (x : ℝ)⁻¹ ≤ Hn N / g := by
  have hsub : (Icc 1 N).filter (g ∣ ·) ⊆ (Icc 1 N).image (g * ·) := by
    intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkN⟩, b, rfl⟩ := hk
    simp only [mem_image, mem_Icc]
    refine ⟨b, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hk1
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left b (by omega)) hkN
  calc _ ≤ ∑ x ∈ (Icc 1 N).image (g * ·), (x : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ b ∈ Icc 1 N, ((g * b : ℕ) : ℝ)⁻¹ := by
        rw [sum_image]; intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h
    _ = Hn N / g := by
        unfold Hn; rw [sum_div]; apply sum_congr rfl; intro b _
        push_cast; rw [mul_inv, div_eq_mul_inv]; ring
/-- Multiples of `g` up to `N`, counted. -/
theorem card_multiples_le (N g : ℕ) (hg : 1 ≤ g) :
    (((Icc 1 N).filter (g ∣ ·)).card : ℝ) ≤ N / g := by
  have h : ((Icc 1 N).filter (g ∣ ·)).card ≤ N / g := by
    have : ((Icc 1 N).filter (g ∣ ·)).card ≤ (Icc 1 (N / g)).card := by
      apply card_le_card_of_injOn (fun n => n / g)
      · intro n hn
        simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hn
        simp only [coe_Icc, Set.mem_Icc]
        obtain ⟨⟨h1, h2⟩, b, rfl⟩ := hn
        rw [Nat.mul_div_cancel_left b (by omega)]
        constructor
        · rcases Nat.eq_zero_or_pos b with h | h
          · subst h; simp at h1
          · exact h
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [Nat.mul_comm g b])
      · intro a ha b hb hab
        simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
        simp only at hab
        obtain ⟨_, a', rfl⟩ := ha
        obtain ⟨_, b', rfl⟩ := hb
        rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)] at hab
        rw [hab]
    simpa using this
  calc (((Icc 1 N).filter (g ∣ ·)).card : ℝ) ≤ ((N / g : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ N / g := Nat.cast_div_le
/-- `Σ_{x, y ≤ N} 1/[x, y] ≤ H_N³`. -/
theorem sum_inv_lcm_le (N : ℕ) :
    ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ((Nat.lcm x y : ℕ) : ℝ)⁻¹ ≤ Hn N ^ 3 := by
  have hpt : ∀ x ∈ Icc 1 N, ∀ y ∈ Icc 1 N, ((Nat.lcm x y : ℕ) : ℝ)⁻¹ ≤
      ∑ g ∈ (Icc 1 N).filter (fun g => g ∣ x ∧ g ∣ y), (g : ℝ) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) := by
    intro x hx y hy
    have hx1 := (mem_Icc.mp hx).1
    have hy1 := (mem_Icc.mp hy).1
    have hgl : (Nat.gcd x y : ℝ) * (Nat.lcm x y : ℝ) = x * y := by exact_mod_cast Nat.gcd_mul_lcm x y
    have hl0 : (0 : ℝ) < Nat.lcm x y := by exact_mod_cast Nat.lcm_pos (by omega) (by omega)
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy1
    have e : ((Nat.lcm x y : ℕ) : ℝ)⁻¹ = (Nat.gcd x y : ℝ) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) := by
      field_simp; linarith
    rw [e]
    have hmem : Nat.gcd x y ∈ (Icc 1 N).filter (fun g => g ∣ x ∧ g ∣ y) := by
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨Nat.gcd_pos_of_pos_left y (by omega), ?_⟩, Nat.gcd_dvd_left x y,
        Nat.gcd_dvd_right x y⟩
      exact (Nat.gcd_le_left y (by omega)).trans (mem_Icc.mp hx).2
    exact single_le_sum (f := fun g : ℕ => (g : ℝ) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹))
      (fun _ _ => by positivity) hmem
  calc _ ≤ ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ g ∈ (Icc 1 N).filter (fun g => g ∣ x ∧ g ∣ y),
        (g : ℝ) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) := by
        apply sum_le_sum; intro x hx; apply sum_le_sum; intro y hy; exact hpt x hx y hy
    _ = ∑ g ∈ Icc 1 N, (g : ℝ) * ((∑ x ∈ (Icc 1 N).filter (g ∣ ·), (x : ℝ)⁻¹) *
          (∑ y ∈ (Icc 1 N).filter (g ∣ ·), (y : ℝ)⁻¹)) := by
        have hg : ∀ g : ℕ, ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N,
            (if g ∣ x ∧ g ∣ y then (g : ℝ) * ((x : ℝ)⁻¹ * (y : ℝ)⁻¹) else 0) =
            (g : ℝ) * ((∑ x ∈ Icc 1 N, if g ∣ x then (x : ℝ)⁻¹ else 0) *
              (∑ y ∈ Icc 1 N, if g ∣ y then (y : ℝ)⁻¹ else 0)) := by
          intro g
          rw [sum_mul_sum, mul_sum]
          apply sum_congr rfl; intro x _
          rw [mul_sum]
          apply sum_congr rfl; intro y _
          by_cases h1 : g ∣ x <;> by_cases h2 : g ∣ y <;> simp [h1, h2]
        simp_rw [sum_filter]
        rw [sum_congr rfl (fun x _ => sum_comm)]
        rw [sum_comm]
        exact sum_congr rfl (fun g _ => hg g)
    _ ≤ ∑ g ∈ Icc 1 N, (g : ℝ) * ((Hn N / g) * (Hn N / g)) := by
        apply sum_le_sum; intro g hg
        have hg1 := (mem_Icc.mp hg).1
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := sum_inv_multiples_le N g hg1
        exact mul_le_mul h h (sum_nonneg (fun _ _ => by positivity)) (by
          have := Hn_nonneg N; positivity)
    _ = Hn N ^ 2 * Hn N := by
        unfold Hn
        rw [mul_sum]; apply sum_congr rfl; intro g hg
        have : (0 : ℝ) < g := by exact_mod_cast (mem_Icc.mp hg).1
        field_simp
    _ = Hn N ^ 3 := by ring
theorem divisors_eq_filter (N n : ℕ) (hn : n ∈ Icc 1 N) :
    n.divisors = (Icc 1 N).filter (· ∣ n) := by
  have h1 := (mem_Icc.mp hn).1
  have h2 := (mem_Icc.mp hn).2
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans h2⟩, hd⟩
  · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
/-- `Σ_{n ≤ N} w(n) d(n)² ≤ c H_N³` when every `Σ_{n ≤ N, L ∣ n} w(n) ≤ c/L`. -/
theorem sum_w_sq_le (N : ℕ) (w : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hG : ∀ L : ℕ, 1 ≤ L → ∑ n ∈ (Icc 1 N).filter (L ∣ ·), w n ≤ c / L) :
    ∑ n ∈ Icc 1 N, w n * (n.divisors.card : ℝ) ^ 2 ≤ c * Hn N ^ 3 := by
  have e1 : ∑ n ∈ Icc 1 N, w n * (n.divisors.card : ℝ) ^ 2 =
      ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (Nat.lcm x y ∣ ·), w n := by
    have : ∀ n ∈ Icc 1 N, w n * (n.divisors.card : ℝ) ^ 2 =
        ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, if x ∣ n ∧ y ∣ n then w n else 0 := by
      intro n hn
      rw [divisors_eq_filter N n hn, card_filter]
      push_cast
      rw [sq, sum_mul_sum, mul_sum]
      apply sum_congr rfl; intro x _
      rw [mul_sum]
      apply sum_congr rfl; intro y _
      by_cases h1 : x ∣ n <;> by_cases h2 : y ∣ n <;> simp [h1, h2]
    rw [sum_congr rfl this, sum_comm]
    apply sum_congr rfl; intro x _
    rw [sum_comm]
    apply sum_congr rfl; intro y _
    rw [sum_filter]
    apply sum_congr rfl; intro n _
    simp only [Nat.lcm_dvd_iff]
  rw [e1]
  calc _ ≤ ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, c * ((Nat.lcm x y : ℕ) : ℝ)⁻¹ := by
        apply sum_le_sum; intro x hx; apply sum_le_sum; intro y hy
        have hl : 1 ≤ Nat.lcm x y :=
          Nat.lcm_pos (mem_Icc.mp hx).1 (mem_Icc.mp hy).1
        refine (hG _ hl).trans (le_of_eq ?_)
        rw [div_eq_mul_inv]
    _ = c * ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ((Nat.lcm x y : ℕ) : ℝ)⁻¹ := by
        rw [mul_sum]; apply sum_congr rfl; intro x _; rw [mul_sum]
    _ ≤ c * Hn N ^ 3 := mul_le_mul_of_nonneg_left (sum_inv_lcm_le N) hc
theorem sum_sq_divisors_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ N * Hn N ^ 3 := by
  have := sum_w_sq_le N (fun _ => 1) N (by positivity) (fun L hL => by
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact card_multiples_le N L hL)
  simpa using this
end LeanLab.HeathBrown1985
