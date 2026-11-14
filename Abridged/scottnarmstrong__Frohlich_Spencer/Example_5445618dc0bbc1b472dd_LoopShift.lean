module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v72c9b17648f2.FroehlichSpencer.FS82.Wilson.ShiftProfile ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The transverse profile of the explicit loop shift

* `uni d` is the uniform weight `1/(d+1)` on `{0,…,d}` and `ramp d` is
  `j/((d+1)(d+2))` on `{1,…,d+1}`; `ramp d (j+1) - ramp d j = uni d j - uni (d+1) j`.
* `levelTwo d`, `levelThree d` are the two components of the level field `b_d` in the
  transverse `2–3` plane, with `curl b_d = u_d ⊗ u_d - u_{d+1} ⊗ u_{d+1}`.
* `shiftTwo d`, `shiftThree d` are the components of `a_d = Σ_{j<d} b_j`, with
  `curl a_d = u_0 ⊗ u_0 - u_d ⊗ u_d`: the unit flux of one plaquette is spread
  uniformly over the square `{0,…,d}²`.
* The squared norms are bounded over every finite index set, and the tent sums used for
  the perimeter bookkeeping are bounded.
-/
public section
namespace FroehlichSpencer.FS82.Wilson
open Finset

/-- `X_d`: the ramp `j/((d+1)(d+2))` on `{1,…,d+1}`. -/
@[expose] noncomputable def ramp (d : ℕ) (j : ℤ) : ℝ :=
  if 1 ≤ j ∧ j ≤ (d : ℤ) + 1 then (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) else 0

/-! ### Sums over arbitrary finite index sets -/

/-- The squared norm of the ramp, `(2d+3)/(6(d+1)(d+2))`. -/
@[expose] noncomputable def rampNormSq (d : ℕ) : ℝ :=
  (2 * (d : ℝ) + 3) / (6 * ((d : ℝ) + 1) * ((d : ℝ) + 2))

/-! ### The level field and the shift in the transverse plane -/

/-! ### Squared norms in the transverse plane -/

/-- The bound `(1/3) (1/(d+1)² + 1/(d+2)²)` for the squared norm of the level field `b_d`. -/
@[expose] noncomputable def levelBound (d : ℕ) : ℝ :=
  (1 / 3) * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2)

/-! ### Series and tent sums -/

end FroehlichSpencer.FS82.Wilson
end

end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_5445618dc0bbc1b472dd_LoopShift ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The explicit loop shift on `ℤ⁴` and its energy

The explicit shift `α` has components along the axes 2 and 3 only,
`α_j(y) = a_{depth(y₀,y₁), j}(y₂, y₃)`, where `depth` is the distance of the column from the
boundary of the sheet and `a_d` is the transverse shift of `ShiftProfile`.

The main result is `loopEnergy_le`: the sum of the squares of the components of `σ - dα`
over any finite box is at most `6 (L + T)`.
-/
public section
namespace FroehlichSpencer.FS82.Wilson
open Finset

/-! ### Depth bookkeeping -/

/-! ### The components of `σ - dα` -/

/-- Bound for the wall between the columns `(y₀, y₁)` and `(y₀ + 1, y₁)`. -/
@[expose] noncomputable def wallBound₀ (L T : ℕ) (y₀ y₁ : ℤ) : ℝ :=
  if (1 ≤ y₀ ∧ y₀ ≤ ((L - 1 : ℕ) : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ (T : ℤ)) then
    levelBound (min (y₀ - 1) ((L : ℤ) - 1 - y₀)).toNat
  else 0

/-! ### Sums over the columns -/


set_option linter.unusedVariables false in
theorem sum_wallBound₀_le (L T : ℕ) (s t : Finset ℤ) 
    (h_FroehlichSpencer_FS82_Wilson_tent_levelBound_sum_le : ∀ (m : ℕ),
      ∑ y ∈ Finset.range (m + 1), FroehlichSpencer.FS82.Wilson.levelBound (Min.min y (m - y)) ≤ 2)
    (h_FroehlichSpencer_FS82_Wilson_wallBound₀_nonneg : ∀ (L T : ℕ) (y₀ y₁ : ℤ), 0 ≤ FroehlichSpencer.FS82.Wilson.wallBound₀ L T y₀ y₁)
    (h_FroehlichSpencer_FS82_Wilson_sum_sum_le_sum_range_of_rect : ∀ (f : ℤ → ℤ → ℝ),
      (∀ (a b : ℤ), 0 ≤ f a b) →
        ∀ (n m : ℕ),
          (∀ (a b : ℤ), f a b ≠ 0 → (1 ≤ a ∧ a ≤ (↑n : ℤ)) ∧ 1 ≤ b ∧ b ≤ (↑m : ℤ)) →
            ∀ (s t : Finset ℤ),
              ∑ a ∈ s, ∑ b ∈ t, f a b ≤
                ∑ k ∈ Finset.range n, ∑ k' ∈ Finset.range m, f ((↑k : ℤ) + 1) ((↑k' : ℤ) + 1))
    :
    ∑ y₀ ∈ s, ∑ y₁ ∈ t, wallBound₀ L T y₀ y₁ ≤ 2 * (T : ℝ) := by
  have h := h_FroehlichSpencer_FS82_Wilson_sum_sum_le_sum_range_of_rect (wallBound₀ L T) (h_FroehlichSpencer_FS82_Wilson_wallBound₀_nonneg L T) (L - 1) T
    (by
      intro a b hab
      by_contra hc
      exact hab (by unfold wallBound₀; rw [ite_eq_right hc])) s t
  refine h.trans ?_
  rcases Nat.lt_or_ge L 2 with hL | hL
  · have h0 : L - 1 = 0 := by omega
    rw [h0]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have hrange : m + 2 - 1 = m + 1 := by omega
  rw [hrange]
  have hterm : ∀ k ∈ range (m + 1), ∀ k' ∈ range T,
      wallBound₀ (m + 2) T ((k : ℤ) + 1) ((k' : ℤ) + 1) = levelBound (min k (m - k)) := by
    intro k hk k' hk'
    have hk1 : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk2 : k' < T := mem_range.mp hk'
    have hmem : (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ ((m + 2 - 1 : ℕ) : ℤ)) ∧
        (1 ≤ (k' : ℤ) + 1 ∧ (k' : ℤ) + 1 ≤ (T : ℤ)) := by omega
    have hmin : (min ((k : ℤ) + 1 - 1) (((m + 2 : ℕ) : ℤ) - 1 - ((k : ℤ) + 1))).toNat =
        min k (m - k) := by omega
    unfold wallBound₀
    rw [ite_eq_left hmem, hmin]
  calc ∑ k ∈ range (m + 1), ∑ k' ∈ range T,
        wallBound₀ (m + 2) T ((k : ℤ) + 1) ((k' : ℤ) + 1)
      = ∑ k ∈ range (m + 1), ∑ k' ∈ range T, levelBound (min k (m - k)) :=
        sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => hterm k hk k' hk'
    _ = (T : ℝ) * ∑ k ∈ range (m + 1), levelBound (min k (m - k)) := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ (T : ℝ) * 2 := by
        gcongr
        exact h_FroehlichSpencer_FS82_Wilson_tent_levelBound_sum_le m
    _ = 2 * (T : ℝ) := by ring

end FroehlichSpencer.FS82.Wilson
end
