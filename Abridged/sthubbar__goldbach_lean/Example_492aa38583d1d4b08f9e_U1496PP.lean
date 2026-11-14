module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.Statements ====
public section
/-!
# Halupczok 2012: basic objects and the statement of Theorem 1.2

K. Halupczok, *Goldbach's problem with primes in arithmetic progressions and in short intervals*,
J. Théor. Nombres Bordeaux 25, 2013, no. 2, 331 to 351, arXiv 1212.4406. This file defines the
sums, the singular series `S` and `T` and the statement `Theorem2` of the paper's Theorem 1.2,
called Theorem 2 in the arXiv version, in its coprime reading. AI wrote the Lean code, Claude,
Anthropic; it was checked by the Lean kernel. Binary Goldbach is open; ternary Goldbach is a
theorem, Helfgott 2013.

Conventions, following the paper's notation section.
* `[X, X+Y]` is the set of integers `m` with `X < m ≤ X + Y`.
* `L = log Y`.
* Every `≪`, `≫`, `≍` in a hypothesis is encoded by a universally quantified constant `c > 0`;
  every `≪` in a conclusion by an existential constant `C`, and "sufficiently large" by an
  existential threshold `Y0`. These may depend on `A`, the `ε`'s, the hypothesis constants and
  the fixed residue `a`. `B = B(A)` is existential after `A`.
-/
@[expose] public section
open Finset
open scoped Classical
namespace LeanLab.Halupczok2012
/-! ### Basic objects -/
/-- The integers `k` in the paper's interval `[X, X+R]`, that is `X < k ≤ X + R`. -/
noncomputable def kRange (X R : ℝ) : Finset ℕ :=
  (Icc 0 ⌈X + R⌉₊).filter (fun k => X < k ∧ (k : ℝ) ≤ X + R)
/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`, with the extra condition `p2 ≡ a2 (q2)`. -/
noncomputable def binSumAP (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    Real.log p * Real.log ((m - p : ℕ) : ℝ)
/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`. -/
noncomputable def binSum (X2 Y : ℝ) (m : ℕ) : ℝ := binSumAP X2 Y 1 0 m
/-- The twin prime type constant `∏_{p ≠ 2} (1 - 1/(p-1)^2)`, as a `tprod` over all primes.
The product converges absolutely, so `tprod` is its value. -/
noncomputable def twinC : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)
/-- The binary singular series `S(r)` of the paper, display 2. -/
noncomputable def S (r : ℕ) : ℝ :=
  if Even r then 2 * twinC * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

end LeanLab.Halupczok2012

end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_492aa38583d1d4b08f9e_U1496PP ====
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

/-! ## Part 3. Indicator identities -/

/-! ## Part 4. Elementary bounds -/

/-! ### The singular series is at most `2^17 r^{1/4}` -/

/-! ## Part 5. The pointwise decomposition -/
axiom mem_kRange' {X R : ℝ} {k : ℕ} (hk : k ∈ kRange X R) : X < k ∧ (k : ℝ) ≤ X + R
axiom kRange_mono {X R R' : ℝ} (h : R ≤ R') : kRange X R ⊆ kRange X R'
axiom card_kRange_le {X R : ℝ} (hR : 0 ≤ R) : ((kRange X R).card : ℝ) ≤ R + 1
/-- **Pointwise.** For `m = 2k`, `X₁ < k ≤ X₁ + R`, `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y`: the
Halupczok error at `2k` minus the difference of the two PP1993 errors at
`N = 2X₁`, `Y' = 2X₁ - X₂` and `Y' = 2X₁ - X₂ - Y` is at most
`2(2R+1) log² m + 8 log³ m · m^{1/2} + 2^17 m^{1/4}`. -/
axiom pointwise {X1 X2 Y R : ℝ} {k : ℕ} (hk : k ∈ kRange X1 R) (hY : 0 < Y) (hX2 : 0 ≤ X2)
    (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y) :
    |(binSum X2 Y (2 * k) - S (2 * k) * Y) -
        ((ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) -
          (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
            S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)))| ≤
      2 * (2 * R + 1) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 +
        8 * Real.log ((2 * k : ℕ) : ℝ) ^ 3 * ((2 * k : ℕ) : ℝ) ^ (1 / 2 : ℝ) +
        2 ^ 17 * ((2 * k : ℕ) : ℝ) ^ (1 / 4 : ℝ)
/-! ## Part 6. The core sum over one window -/
/-- The error bound `Emax` at the top `M = 2X₁ + 2R` of the window. -/
noncomputable def Emax (R M : ℝ) : ℝ :=
  2 * (2 * R + 1) * Real.log M ^ 2 + 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ) +
    2 ^ 17 * M ^ (1 / 4 : ℝ)
axiom sq_three (a b c : ℝ) : (a - b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2
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
