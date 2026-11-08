/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Examples.rwst__Confinement_Certificates.Dependencies.v52492122af6e.FLP.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Escape of the origin ⟹ the survivor set is finite (FLP95, Theorem 3.4, weakened)

For the theorem of Flatto–Lagarias–Pollington only *finiteness* of the survivor set
`S_{β,α} = {x ∈ [0,1/β) : f^n(x) < 1/β for all n}` is needed, not the sharp count.  This file
proves it, for an arbitrary real base `β > 1` and offset `α ∈ [0,1)`, under the single hypothesis
that the **origin escapes**: some iterate `f^N(0) ≥ 1/β`.

The proof is the measure-free redesign of `plan-FLT.html` §4 (numerically verified 120/120 there):

* **Cylinders.** For a branch word `w`, `cyl w` is the set of points whose first `|w|` branches
  follow `w`.  Each `cyl w` is order-connected (`cyl_ordConnected`), and the two branches of `f`
  restrict to increasing affine bijections `[0,c) → [α,1)` and `[c,1/β) → [0,α)` (`c = (1-α)/β`),
  so a nonempty cylinder has **two** nonempty children iff it *straddles* `α` — meets both `[0,α)`
  and `[α,1)` — and **one** otherwise.
* **The count is bounded by `N`.** A straddling cylinder contains `α` (order-connectedness), and
  distinct cylinders are disjoint, so at most one cylinder straddles per depth
  (`straddle_filter_card_le_one`).  Since `f(0) = α`, a straddle at depth `m` forces `0`'s orbit
  `f, f², …, f^m` to stay in `J`, impossible once `m ≥ N`.  Hence the number of nonempty depth-`m`
  cylinders never exceeds `N + 1` (`alive_card_le`).
* **Expansivity + separation.** Two survivors sharing their first `m` branches differ by
  `< (1/β)^m` (the branch maps have slope `β`, `iter_sub_eq`), so distinct survivors eventually
  get distinct depth-`m` words.  A set of `> N+1` survivors would therefore realize `> N+1`
  nonempty cylinders at some depth — a contradiction.  Thus `survivors` is finite.

## References

* [FLP95] Flatto–Lagarias–Pollington, Acta Arith. **70.2** (1995), 125–147, Theorem 3.4 (only the
  finiteness of `S_{β,α}` is used; the measure-theoretic argument there is replaced by the
  cylinder split-count above).
-/
set_option linter.unusedSectionVars false
namespace FLP
open Set
open scoped Classical
noncomputable def word (β α : ℝ) (x : ℝ) (m : ℕ) : List Bool :=
  (List.range m).map (fun k => decide (splitPt β α ≤ (lmo β α)^[k] x))
variable {β α : ℝ}
/-! ## Word combinatorics (hypothesis-free) -/
theorem word_length (x : ℝ) (m : ℕ) : (word β α x m).length = m := by simp [word]
theorem word_succ_eq (x : ℝ) (m : ℕ) :
    word β α x (m + 1) = word β α x m ++ [decide (splitPt β α ≤ (lmo β α)^[m] x)] := by
  simp only [word, List.range_succ, List.map_append, List.map_cons, List.map_nil]
section
variable (hβ : 1 < β) (hα0 : 0 ≤ α) (hα1 : α < 1)
include hβ hα0 hα1
/-! ## Geometry of the split point and branches -/
theorem lmo_lower {x : ℝ} (hx0 : 0 ≤ x) (hxc : x < splitPt β α) : lmo β α x = β * x + α := by
  apply lmo_of_lt (by positivity)
  have h : β * x < β * splitPt β α := mul_lt_mul_of_pos_left hxc (by linarith)
  rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at h; linarith
/-- Upper branch: `f(x) = βx + α - 1` on `[c, 1/β)`. -/
theorem lmo_upper {x : ℝ} (hxc : splitPt β α ≤ x) (hx1 : x < 1 / β) : lmo β α x = β * x + α - 1 := by
  apply lmo_of_ge
  · have h : β * splitPt β α ≤ β * x := mul_le_mul_of_nonneg_left hxc (by linarith)
    rw [splitPt, mul_div_cancel₀ _ (by linarith : β ≠ 0)] at h; linarith
  · have h : β * x < β * (1 / β) := mul_lt_mul_of_pos_left hx1 (by linarith)
    rw [mul_one_div, div_self (by linarith : β ≠ 0)] at h; linarith
theorem lmo_diff {u v : ℝ} (hu : u ∈ Ico (0 : ℝ) (1 / β)) (hv : v ∈ Ico (0 : ℝ) (1 / β))
    (hb : decide (splitPt β α ≤ u) = decide (splitPt β α ≤ v)) :
    lmo β α u - lmo β α v = β * (u - v) := by
  have hiff : (splitPt β α ≤ u) ↔ (splitPt β α ≤ v) := decide_eq_decide.mp hb
  by_cases hcu : splitPt β α ≤ u
  · rw [lmo_upper hβ hα0 hα1 hcu hu.2, lmo_upper hβ hα0 hα1 (hiff.mp hcu) hv.2]; ring
  · have hcv : ¬ splitPt β α ≤ v := fun h => hcu (hiff.mpr h)
    push Not at hcu hcv
    rw [lmo_lower hβ hα0 hα1 hu.1 hcu, lmo_lower hβ hα0 hα1 hv.1 hcv]; ring
/-- Same first `m` branches ⟹ the two points differ by exactly `β^m·(x−y)`. -/
theorem iter_sub_eq {x y : ℝ} (hx : ∀ n, (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β))
    (hy : ∀ n, (lmo β α)^[n] y ∈ Ico (0 : ℝ) (1 / β)) :
    ∀ m, word β α x m = word β α y m →
      (lmo β α)^[m] x - (lmo β α)^[m] y = β ^ m * (x - y) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hw
      rw [word_succ_eq, word_succ_eq] at hw
      obtain ⟨hpre, htail⟩ := List.append_inj hw (by rw [word_length, word_length])
      have hlast : decide (splitPt β α ≤ (lmo β α)^[m] x)
          = decide (splitPt β α ≤ (lmo β α)^[m] y) := by simpa using htail
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        lmo_diff hβ hα0 hα1 (hx m) (hy m) hlast, ih hpre, pow_succ]
      ring
/-- Distinct survivors have distinct itineraries (expansivity). -/
theorem eq_of_word_eq {x y : ℝ} (hx : ∀ n, (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β))
    (hy : ∀ n, (lmo β α)^[n] y ∈ Ico (0 : ℝ) (1 / β))
    (h : ∀ m, word β α x m = word β α y m) : x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt1 : (1 : ℝ) / β < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos hlt1
  have hsub := iter_sub_eq hβ hα0 hα1 hx hy m (h m)
  have hb : |(lmo β α)^[m] x - (lmo β α)^[m] y| < 1 / β := by
    obtain ⟨a1, a2⟩ := hx m; obtain ⟨b1, b2⟩ := hy m
    rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
  rw [hsub, abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < β) m)] at hb
  have h2 : |x - y| < (1 / β) ^ (m + 1) := by
    rw [div_pow, one_pow, lt_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < β) (m + 1)), pow_succ]
    have hmul := mul_lt_mul_of_pos_left hb (show (0 : ℝ) < β by linarith)
    rw [mul_one_div, div_self (by linarith : β ≠ 0)] at hmul
    nlinarith [hmul]
  have h3 : (1 / β) ^ (m + 1) ≤ (1 / β) ^ m := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (le_of_lt (one_div_pos.mpr (by linarith))) m)
      (le_of_lt hlt1)
  linarith
/-! ## The survivor set is finite -/
end
end FLP
