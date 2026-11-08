module
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.Statements
/-!
# P0077 Halupczok 2012, Theorem 2: combinatorial steps of the reduction, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `ternSum_eq`: the ternary sum of Theorem 2 is `∑_{p₁} log p₁ · binSum(n - p₁)`, the
  substitution `2k₁ = n - p₁` of the paper's proof of Theorem 2.
* `card_cong_le`: at most `y/l + 1` integers of a window of length `y` lie in one class mod `l`.
* `sum_inv_lcm_le`: `∑_{q₁, q₂ ≤ Q} 1/[q₁, q₂] ≤ (1 + log Q)³`.
* `divisor_moment`: `∑_{m ∈ W} (#{q ≤ Q : q ∣ m - a})² ≤ y (1 + log Q)³ + Q²` for `W` inside a
  window of length `y`.
* `sum_q_abs_sq_le`: Cauchy-Schwarz,
  `(∑_{q ≤ Q} |∑_{m ∈ W, m ≡ a (q)} w m|)² ≤ (∑_{m∈W} w m²) · ∑_{m∈W} (#{q ≤ Q : m ≡ a (q)})²`.
  For `Q² ≪ y` this replaces the paper's Lemma 1, which is needed only for larger `Q`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
theorem card_cong_le {S : Finset ℕ} {x y : ℝ} {l : ℕ} (hl : 0 < l) (hy : 0 ≤ y)
    (hS : ∀ m ∈ S, x < m ∧ (m : ℝ) ≤ x + y)
    (hc : ∀ m ∈ S, ∀ m' ∈ S, (m : ℤ) ≡ (m' : ℤ) [ZMOD l]) :
    (S.card : ℝ) ≤ y / l + 1 := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  rcases S.eq_empty_or_nonempty with h | hne
  · simp [h]; positivity
  set m0 := S.min' hne with hm0
  have hm0S : m0 ∈ S := S.min'_mem hne
  have key : ∀ m ∈ S, m0 ≤ m ∧ l ∣ m - m0 ∧ (((m - m0) / l : ℕ) : ℝ) ≤ y / l := by
    intro m hm
    have hle : m0 ≤ m := S.min'_le m hm
    have hd : l ∣ m - m0 := by
      have := (hc m0 hm0S m hm).dvd
      rw [← Int.natCast_dvd_natCast, Nat.cast_sub hle]
      exact this
    refine ⟨hle, hd, ?_⟩
    rw [le_div_iff₀ hl']
    have h1 : (((m - m0) / l : ℕ) : ℝ) * l = ((m - m0 : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
    rw [h1, Nat.cast_sub hle]
    have := (hS m hm).2
    have := (hS m0 hm0S).1
    linarith
  have hinj : Set.InjOn (fun m => (m - m0) / l) S := by
    intro m hm m' hm' he
    simp only at he
    obtain ⟨h1, h2, -⟩ := key m hm
    obtain ⟨h1', h2', -⟩ := key m' hm'
    have e1 := Nat.div_mul_cancel h2
    have e2 := Nat.div_mul_cancel h2'
    rw [he] at e1
    omega
  have hmaps : Set.MapsTo (fun m => (m - m0) / l) S (range (⌊y / l⌋₊ + 1)) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    have := (key m hm).2.2
    have := Nat.le_floor this
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  calc (S.card : ℝ) ≤ ((⌊y / l⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ y / l + 1 := by
      push_cast
      have := Nat.floor_le (div_nonneg hy hl'.le)
      linarith
end LeanLab.Halupczok2012
