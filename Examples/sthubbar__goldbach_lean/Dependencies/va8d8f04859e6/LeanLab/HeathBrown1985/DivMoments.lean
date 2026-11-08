module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Lemma2
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
end LeanLab.HeathBrown1985
