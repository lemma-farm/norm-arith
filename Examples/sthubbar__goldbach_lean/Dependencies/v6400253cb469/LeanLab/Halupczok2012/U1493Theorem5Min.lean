module
public import Examples.sthubbar__goldbach_lean.Dependencies.v6400253cb469.LeanLab.Halupczok2012.U1462Tails
/-!
# P0077 Halupczok 2012, `Theorem5` shrunk to its minimal window scale, unit U-1493

AI wrote the Lean code, Claude, run 20261022T1603Z-23862. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

`Theorem5` is the paper's adaptation of Perelli-Pintz 1993, arXiv 1212.4406v1 Theorem 5, journal
JTNB 25 2013 Theorem 2.3 p. 339. It allows every window length `R` with
`c₂ Y^{1/3+ε} ≤ R ≤ c₃ Y`. Here:

* `Theorem5Min`: the same mean square bound, but only for windows of the MINIMAL scale
  `c₂ Y^{1/3+ε} ≤ R ≤ 2 c₂ Y^{1/3+ε}`, an extra hypothesis. A weaker Prop.
* `theorem5_of_min : Theorem5Min → Theorem5`. PROVED, by cutting `[X₁, X₁ + R]` into
  `m = ⌊R / (c₂ Y^{1/3+ε})⌋` windows of length `R/m` and summing.
* `theorem5Min_of_theorem5 : Theorem5 → Theorem5Min`. PROVED, so the two are equivalent.
* `theorem2Zeroed_U1493`: the F-0008 repair CONDITIONAL ON `Theorem3` and `Theorem5Min`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
theorem floor_pieces {R R0 : ℝ} (hR0 : 0 < R0) (h : R0 ≤ R) :
    1 ≤ ⌊R / R0⌋₊ ∧ R0 ≤ R / ⌊R / R0⌋₊ ∧ R / ⌊R / R0⌋₊ ≤ 2 * R0 := by
  set t := R / R0 with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hR0]; linarith
  have hm1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
  have hmR : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hRt : R = t * R0 := by rw [ht]; field_simp
  refine ⟨hm1, ?_, ?_⟩
  · rw [le_div_iff₀ hmpos, hRt]; nlinarith
  · rw [div_le_iff₀ hmpos, hRt]; nlinarith
end LeanLab.Halupczok2012
