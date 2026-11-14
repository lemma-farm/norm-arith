import Mathlib.Algebra.Order.Round
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

-- ==== Examples.rwst__Confinement_Certificates.Dependencies.v52492122af6e.FLP.Basic ====
section
/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The Flatto–Lagarias–Pollington ⅓-spread theorem: core objects (FLP95)

Stage 0 of the FLP program (`plan-FLT.html`): the arithmetic and dynamical objects that
underlie Flatto–Lagarias–Pollington's theorem that for coprime `p > q ≥ 2` the orbit
`{ξ(p/q)ⁿ}` has range spread `≥ 1/p` for *every* `ξ > 0` (their Theorem 1.4; the `3/2`
case is milestone **M3** of the `report2-weyl` §5 ladder).

The proof (see `plan-FLT.html` §2–4) decouples the real orbit into an integer part driven by
the **`T`-map** `T(g) = ⌈(pg+a)/q⌉` and a fractional part driven by the **linear mod-one
transformation** `f_{β,α}(x) = {βx + α}`.  This file fixes those two objects and the sets they
act on, and proves the elementary structural facts everything downstream consumes:

* the fractional map `lmo β α` lands in `[0,1)` and, restricted to `J = [0,1/β)`, is a pair of
  increasing affine branches split at `c = (1-α)/β` (its images are `[α,1)` and `[0,α)`);
* the ceiling map `TMap` has the exact linearization `q·T(g) = pg + a + i_g` with the symbol
  `i_g := iSym ∈ [0,q)` (`TMap_mul`, `iSym_lt`), the congruence `i_g ≡ -(pg+a) (mod q)`
  (`iSym_add_modEq`), and the key shift identity `T(g + qi) = T(g) + pi` (`TMap_add_qmul`)
  that powers the `T`-expansion injectivity of `FLP.TExpansion`.

Everything here is fractional-part / `ℕ`-division bookkeeping — no measure theory, no
transcendence input.  The target footprint of the whole `FLP/` root is the standard three
axioms.

## Contents

* `FLP.lmo` — the linear mod-one map `f_{β,α}`; `lmo_mem_Ico`, `lmo_iterate_succ_mem_Ico`,
  branch lemmas `lmo_of_lt`/`lmo_of_ge`, `lmo_zero`.
* `FLP.survivors` — the survivor set `S_{β,α} = {x ∈ [0,1/β) : fⁿx < 1/β ∀n}`.
* `FLP.ZSet` — the `Z`-set `Z_{p/q}(s,s+t) = {ξ>0 : {ξ(p/q)ⁿ} ∈ [s,s+t) ∀n}`.
* `FLP.TMap`, `FLP.iSym` — the integer dynamics and its symbol; `TMap_mul`, `iSym_lt`,
  `iSym_add_modEq`, `TMap_add_qmul`.

## References

* [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts
  `{ξ(p/q)ⁿ}`*, Acta Arithmetica **70.2** (1995), 125–147.  (`aa7023.pdf`; §2 for the
  decoupling, §3 for the `Z`-set / survivor machinery.)
-/
namespace FLP
open Set
/-! ## The linear mod-one transformation `f_{β,α}` -/
/-- The **linear mod-one transformation** `f_{β,α}(x) = {βx + α}` (FLP §2), the fractional-part
dynamics that drives the `θ`-coordinate of a trapped orbit. -/
noncomputable def lmo (β α x : ℝ) : ℝ := Int.fract (β * x + α)
/-- The split point `c = (1-α)/β` of `f_{β,α}` on `J = [0,1/β)`: below `c` the map is `βx+α`
(image `[α,1)`), at or above it the map is `βx+α-1` (image `[0,α)`). -/
noncomputable def splitPt (β α : ℝ) : ℝ := (1 - α) / β

/-! ## The survivor and `Z` sets -/

end FLP

end

-- ==== Examples.rwst__Confinement_Certificates.Examples.Example_c99511b983e5cb98db40_SurvivorFinite ====
/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
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

section
variable (hβ : 1 < β) (hα0 : 0 ≤ α) (hα1 : α < 1)
include hβ hα0 hα1
/-! ## Geometry of the split point and branches -/


set_option linter.unusedVariables false in
/-- Distinct survivors have distinct itineraries (expansivity). -/
theorem eq_of_word_eq {x y : ℝ} (hx : ∀ n, (lmo β α)^[n] x ∈ Ico (0 : ℝ) (1 / β))
    (hy : ∀ n, (lmo β α)^[n] y ∈ Ico (0 : ℝ) (1 / β))
    (h : ∀ m, word β α x m = word β α y m) 
    (h_FLP_iter_sub_eq : ∀ {β α : ℝ},
      1 < β →
        0 ≤ α →
          α < 1 →
            ∀ {x y : ℝ},
              (∀ (n : ℕ), (FLP.lmo β α)^[n] x ∈ Set.Ico 0 (1 / β)) →
                (∀ (n : ℕ), (FLP.lmo β α)^[n] y ∈ Set.Ico 0 (1 / β)) →
                  ∀ (m : ℕ),
                    FLP.word β α x m = FLP.word β α y m →
                      (FLP.lmo β α)^[m] x - (FLP.lmo β α)^[m] y = β ^ m * (x - y))
    : x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt1 : (1 : ℝ) / β < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos hlt1
  have hsub := h_FLP_iter_sub_eq hβ hα0 hα1 hx hy m (h m)
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
