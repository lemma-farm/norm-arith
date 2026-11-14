module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.va0f526aeba09.LeanLab.Halupczok2012.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_8a3f97c6226b8e90a0a2_U1496PP ====
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
def PP1993Goldbach : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        (ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y) ^ 2 ≤
      C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A)
/-! ### Vacuity -/

/-! ## Part 3. Indicator identities -/

/-! ## Part 4. Elementary bounds -/

/-! ### The singular series is at most `2^17 r^{1/4}` -/

/-! ## Part 5. The pointwise decomposition -/

/-! ## Part 6. The core sum over one window -/
/-- The error bound `Emax` at the top `M = 2X₁ + 2R` of the window. -/
noncomputable def Emax (R M : ℝ) : ℝ :=
  2 * (2 * R + 1) * Real.log M ^ 2 + 8 * Real.log M ^ 3 * M ^ (1 / 2 : ℝ) +
    2 ^ 17 * M ^ (1 / 4 : ℝ)

/-- **Core.** One window `X₁ < k ≤ X₁ + R` with `2R ≤ Y`, `2R ≤ 2X₁ - X₂ - Y` and `R` at most half
of both PP1993 window lengths `(2X₁ - X₂)^a` and `(2X₁ - X₂ - Y)^a`: the Halupczok mean square is
at most three times the two PP1993 mean squares plus `3 (R + 1) Emax²`. -/
axiom core_sum {X1 X2 Y R a Bhi Blo : ℝ}
    (hhi : ∑ k ∈ kRange X1 ((2 * X1 - X2) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2) - S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2)) ^ 2
        ≤ Bhi)
    (hlo : ∑ k ∈ kRange X1 ((2 * X1 - X2 - Y) ^ a / 2),
      (ppR (2 * k) (2 * X1) (2 * X1 - X2 - Y) -
        S (2 * k) * ppM (2 * k) (2 * X1) (2 * X1 - X2 - Y)) ^ 2 ≤ Blo)
    (hY : 0 < Y) (hX2 : 0 ≤ X2) (hR : 0 ≤ R) (h2R : 2 * R ≤ Y) (hV : 2 * R ≤ 2 * X1 - X2 - Y)
    (hRhi : R ≤ (2 * X1 - X2) ^ a / 2) (hRlo : R ≤ (2 * X1 - X2 - Y) ^ a / 2) :
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      3 * Bhi + 3 * Blo + 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2
/-! ## Part 7. Asymptotics on one window of the minimal scale -/
axiom rpow_natpow {u : ℝ} (hu : 0 ≤ u) (n k : ℕ) {r : ℝ} (h : (n : ℝ) * r = k) :
    (u ^ n) ^ r = u ^ k
/-- `X₂ ≤ c₁^{-12/7} u^{300}` when `c₁ X₂^{7/12+ε₂} ≤ Y = u^{175}`, `X₂ ≥ 1`. -/
axiom x2_le {c1 ε2 X2 Y u : ℝ} (hc1 : 0 < c1) (hε2 : 0 ≤ ε2) (hX21 : 1 ≤ X2)
    (h1 : c1 * X2 ^ (7 / 12 + ε2) ≤ Y) (hYu : Y = u ^ (175 : ℕ)) (hu0 : 0 ≤ u) :
    X2 ≤ (1 / c1) ^ (12 / 7 : ℝ) * u ^ (300 : ℕ)
/-- **The error bound in powers of `u`.** -/
axiom emax_le {c4a KM R M u : ℝ} (hu1 : 1 ≤ u) (hM1 : 1 ≤ M) (hKM0 : 0 ≤ KM)
    (hMu : M ≤ KM * u ^ (300 : ℕ)) (hc4a : 0 ≤ c4a) (hR : 2 * R + 1 ≤ 3 / 2 * (c4a * u ^ (70 : ℕ))) :
    Emax R M ≤ (3 * c4a * (100 * KM ^ (1 / 100 : ℝ)) ^ 2 +
        8 * (100 * KM ^ (1 / 100 : ℝ)) ^ 3 * KM ^ (1 / 2 : ℝ) + 2 ^ 17 * KM ^ (1 / 4 : ℝ)) *
      u ^ (166 : ℕ)
/-- **Logarithm against a power of `u`.** For `Y = u^{175} > 1`:
`u^{332} ≤ (175A/18)^A · Y² (log Y)^{-A}`. -/
axiom logpow_le {A Y u : ℝ} (hA : 0 < A) (hY1 : 1 < Y) (hYu : Y = u ^ (175 : ℕ))
    (hu0 : 0 ≤ u) :
    u ^ (332 : ℕ) ≤ (175 * A / 18) ^ A * (Y ^ 2 * Real.log Y ^ (-A))
/-- **A PP1993 term in Halupczok's units.** -/
axiom ppterm_le {C0 V a A c4 c5 Y X1 R : ℝ} (hA : 0 < A) (hc4 : 0 < c4) (hc5 : 0 < c5)
    (ha : 0 < a)
    (hY1 : 1 < Y) (hYX : Y ≤ 2 * X1) (hV0 : 0 ≤ V) (hVc : V ≤ (c5 + 1) * Y)
    (hR4 : (c4 * Y) ^ a ≤ 4 * R) :
    C0 * V ^ a * V ^ 2 * Real.log (2 * X1) ^ (-A) ≤
      max C0 0 * (4 * ((c5 + 1) / c4) ^ a) * (c5 + 1) ^ 2 * (R * Y ^ 2 * Real.log Y ^ (-A))
set_option maxHeartbeats 1000000 in
/-- **One window.** CONDITIONAL ON `PP1993Goldbach`: the Halupczok mean square over a window of
length `R ≍ (c₄ Y)^{1/3+δ}` is `≪ R Y² L^{-A}`, for `δ ≤ ε₂/2`, `δ ≤ 1/24`. -/
theorem piece (hPP : PP1993Goldbach) {A ε2 δ : ℝ} (hA : 0 < A) (hε2 : 0 < ε2) (hδ : 0 < δ)
    (hδ2 : δ ≤ ε2 / 2) (hδ1 : δ ≤ 1 / 24) {c1 c4 c5 : ℝ} (hc1 : 0 < c1) (hc4 : 0 < c4)
    (hc5 : 0 < c5) :
    ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y → c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 →
      c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
      (c4 * Y) ^ (1 / 3 + δ) / 4 ≤ R → R ≤ (c4 * Y) ^ (1 / 3 + δ) / 2 →
      ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
        C * R * Y ^ 2 * Real.log Y ^ (-A) := by
  obtain ⟨C0, N0, hC0⟩ := hPP δ A hδ hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 3 + δ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 7 / 12 + δ := ⟨_, rfl⟩
  rw [← ha, ← hb] at hC0
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha3 : a ≤ 2 / 5 := by rw [ha]; linarith
  have ha13 : 1 / 3 ≤ a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  obtain ⟨Kpp, hKpp⟩ : ∃ K : ℝ, K = (c5 + 2) ^ b / (c4 * c1) := ⟨_, rfl⟩
  have hKpp0 : 0 ≤ Kpp := by rw [hKpp]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max 1 (max (c4 ^ a) (c4 ^ a / c4)) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact le_trans zero_le_one (le_max_left _ _)
  obtain ⟨KM, hKM⟩ : ∃ K : ℝ, K = (c5 + 3) * (1 / c1) ^ (12 / 7 : ℝ) := ⟨_, rfl⟩
  have hKM0 : 0 ≤ KM := by rw [hKM]; positivity
  obtain ⟨KE, hKE⟩ : ∃ K : ℝ, K = 3 * c4 ^ a * (100 * KM ^ (1 / 100 : ℝ)) ^ 2 +
      8 * (100 * KM ^ (1 / 100 : ℝ)) ^ 3 * KM ^ (1 / 2 : ℝ) + 2 ^ 17 * KM ^ (1 / 4 : ℝ) :=
    ⟨_, rfl⟩
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K : ℝ, K = max C0 0 * (4 * ((c5 + 1) / c4) ^ a) * (c5 + 1) ^ 2 :=
    ⟨_, rfl⟩
  refine ⟨6 * K1 + 6 * KE ^ 2 * (175 * A / 18) ^ A,
    max (max 2 N0) (max (Kpp ^ (2 / ε2)) (max (T ^ (175 : ℕ)) (64 / c4))), ?_⟩
  intro X1 X2 Y R hY0 h1 h2 h4 h5 hR1 hR2
  have hY2 : 2 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY0
  have hYN0 : N0 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY0
  have hYK : Kpp ^ (2 / ε2) ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY0
  have hYT : T ^ (175 : ℕ) ≤ Y :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hY0
  have hY64 : 64 / c4 ≤ Y :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hY0
  have hYpos : 0 < Y := by linarith
  have hX21 : 1 ≤ X2 := by linarith
  -- u = Y^{1/175}
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Y ^ (1 / 175 : ℝ) := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hYu : Y = u ^ (175 : ℕ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]; norm_num
  have huT : T ≤ u := by
    have := Real.rpow_le_rpow (pow_nonneg hT0 175) hYT (show (0 : ℝ) ≤ 1 / 175 by norm_num)
    rw [rpow_natpow hT0 175 1 (by norm_num), pow_one, ← hu] at this
    exact this
  have hupow : ∀ i j : ℕ, i ≤ j → u ^ i ≤ u ^ j := fun i j hij => pow_le_pow_right₀ hu1 hij
  -- (c4 Y)^a
  have hc4a0 : 0 ≤ c4 ^ a := by positivity
  have hYa : Y ^ a ≤ u ^ (70 : ℕ) := by
    calc Y ^ a ≤ Y ^ (2 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha3
      _ = u ^ (70 : ℕ) := by rw [hYu]; exact rpow_natpow hu0 175 70 (by norm_num)
  have hcY : (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := by
    rw [Real.mul_rpow hc4.le hYpos.le]; exact mul_le_mul_of_nonneg_left hYa hc4a0
  have hTa : c4 ^ a ≤ u := by
    refine le_trans ?_ huT; rw [hT]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTa' : c4 ^ a / c4 ≤ u := by
    refine le_trans ?_ huT; rw [hT]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hu105 : u ≤ u ^ (105 : ℕ) := by simpa using hupow 1 105 (by norm_num)
  have hu175 : u ^ (105 : ℕ) * u ^ (70 : ℕ) = u ^ (175 : ℕ) := by rw [← pow_add]
  have hu70 : 0 ≤ u ^ (70 : ℕ) := by positivity
  have hcYY : (c4 * Y) ^ a ≤ Y := by
    calc (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := hcY
      _ ≤ u ^ (105 : ℕ) * u ^ (70 : ℕ) := mul_le_mul_of_nonneg_right (hTa.trans hu105) hu70
      _ = Y := by rw [hu175, hYu]
  have hcYc : (c4 * Y) ^ a ≤ c4 * Y := by
    have e : c4 ^ a ≤ c4 * u ^ (105 : ℕ) := by
      rw [div_le_iff₀ hc4] at hTa'; nlinarith
    calc (c4 * Y) ^ a ≤ c4 ^ a * u ^ (70 : ℕ) := hcY
      _ ≤ c4 * u ^ (105 : ℕ) * u ^ (70 : ℕ) := mul_le_mul_of_nonneg_right e hu70
      _ = c4 * Y := by rw [mul_assoc, hu175, hYu]
  have hcY4 : 4 ≤ (c4 * Y) ^ a := by
    have h64 : (64 : ℝ) ≤ c4 * Y := by rw [div_le_iff₀ hc4] at hY64; linarith
    calc (4 : ℝ) = ((4 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [rpow_natpow (by norm_num) 3 1 (by norm_num), pow_one]
      _ ≤ (c4 * Y) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith)
          (by norm_num)
      _ ≤ (c4 * Y) ^ a := Real.rpow_le_rpow_of_exponent_le (by linarith) ha13
  have hR0 : 1 ≤ R := by linarith
  have h2R : 2 * R ≤ Y := by linarith
  have hV : 2 * R ≤ 2 * X1 - X2 - Y := by linarith
  have hc5X : c5 * Y ≤ c5 * X2 := mul_le_mul_of_nonneg_left h2 hc5.le
  have hc4Y : 0 ≤ c4 * Y := by positivity
  -- M = 2 X1 + 2 R
  have hX2u := x2_le hc1 hε2.le hX21 h1 hYu hu0
  have hM1 : 1 ≤ 2 * X1 + 2 * R := by linarith
  have hMu : 2 * X1 + 2 * R ≤ KM * u ^ (300 : ℕ) := by
    have : 2 * X1 + 2 * R ≤ (c5 + 3) * X2 := by linarith
    calc 2 * X1 + 2 * R ≤ (c5 + 3) * X2 := this
      _ ≤ (c5 + 3) * ((1 / c1) ^ (12 / 7 : ℝ) * u ^ (300 : ℕ)) :=
          mul_le_mul_of_nonneg_left hX2u (by linarith)
      _ = KM * u ^ (300 : ℕ) := by rw [hKM]; ring
  have hR3 : 2 * R + 1 ≤ 3 / 2 * (c4 ^ a * u ^ (70 : ℕ)) := by linarith
  have hEm := emax_le hu1 hM1 hKM0 hMu hc4a0 hR3
  rw [← hKE] at hEm
  -- PP1993 hypotheses at N = 2 X1
  have hN0 : N0 ≤ 2 * X1 := by linarith
  have hXpow : Kpp ≤ X2 ^ (ε2 / 2) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hKpp0 _) (hYK.trans h2)
      (by positivity : 0 ≤ ε2 / 2)
    rwa [← Real.rpow_mul hKpp0, show 2 / ε2 * (ε2 / 2) = 1 by field_simp, Real.rpow_one] at this
  have hNb : (2 * X1) ^ b ≤ 2 * X1 - X2 - Y := by
    have e1 : (2 * X1) ^ b ≤ (c5 + 2) ^ b * X2 ^ b := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hb0.le
    have e2 : X2 ^ b * X2 ^ (ε2 / 2) ≤ X2 ^ (7 / 12 + ε2) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hX21 (by rw [hb]; linarith)
    have e3 : (c5 + 2) ^ b = c4 * c1 * Kpp := by rw [hKpp]; field_simp
    have hXb : 0 ≤ X2 ^ b := by positivity
    have e4 : c4 * c1 * X2 ^ (7 / 12 + ε2) ≤ c4 * Y := by
      have := mul_le_mul_of_nonneg_left h1 hc4.le; linarith
    calc (2 * X1) ^ b ≤ (c5 + 2) ^ b * X2 ^ b := e1
      _ = c4 * c1 * (Kpp * X2 ^ b) := by rw [e3]; ring
      _ ≤ c4 * c1 * (X2 ^ (ε2 / 2) * X2 ^ b) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXpow hXb) (by positivity)
      _ ≤ c4 * c1 * X2 ^ (7 / 12 + ε2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ ≤ c4 * Y := e4
      _ ≤ 2 * X1 - X2 - Y := h4
  have hhi := hC0 (2 * X1) (2 * X1 - X2) hN0 (by linarith) (by linarith)
  have hlo := hC0 (2 * X1) (2 * X1 - X2 - Y) hN0 hNb (by linarith)
  have e2X : 2 * X1 / 2 = X1 := by ring
  rw [e2X] at hhi hlo
  have hRlo : R ≤ (2 * X1 - X2 - Y) ^ a / 2 := by
    have := Real.rpow_le_rpow (by positivity) h4 ha0.le
    linarith
  have hRhi : R ≤ (2 * X1 - X2) ^ a / 2 := by
    have := Real.rpow_le_rpow (by linarith) (show 2 * X1 - X2 - Y ≤ 2 * X1 - X2 by linarith)
      ha0.le
    linarith
  have hcore := core_sum hhi hlo hYpos (by linarith) (by linarith) h2R hV hRhi hRlo
  -- the PP terms
  have hR4 : (c4 * Y) ^ a ≤ 4 * R := by linarith
  have hB1 := ppterm_le (C0 := C0) (X1 := X1) (R := R) (Y := Y) hA hc4 hc5 ha0 (by linarith) (by linarith)
    (show 0 ≤ 2 * X1 - X2 by linarith) (show 2 * X1 - X2 ≤ (c5 + 1) * Y by linarith) hR4
  have hB2 := ppterm_le (C0 := C0) (X1 := X1) (R := R) (Y := Y) hA hc4 hc5 ha0 (by linarith) (by linarith)
    (show 0 ≤ 2 * X1 - X2 - Y by linarith) (show 2 * X1 - X2 - Y ≤ (c5 + 1) * Y by linarith) hR4
  rw [← hK1] at hB1 hB2
  -- the error term
  have hEmax0 : 0 ≤ Emax R (2 * X1 + 2 * R) := by
    unfold Emax
    have := Real.log_nonneg hM1
    positivity
  have hEsq : Emax R (2 * X1 + 2 * R) ^ 2 ≤ KE ^ 2 * u ^ (332 : ℕ) := by
    calc Emax R (2 * X1 + 2 * R) ^ 2 ≤ (KE * u ^ (166 : ℕ)) ^ 2 := pow_le_pow_left₀ hEmax0 hEm 2
      _ = _ := by ring
  have hlp := logpow_le hA (by linarith) hYu hu0
  have hT3 : 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤
      6 * KE ^ 2 * (175 * A / 18) ^ A * (R * Y ^ 2 * Real.log Y ^ (-A)) := by
    have e1 : 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤ 6 * R * (KE ^ 2 * u ^ (332 : ℕ)) := by
      have : 3 * (R + 1) ≤ 6 * R := by linarith
      exact mul_le_mul this hEsq (sq_nonneg _) (by linarith)
    calc 3 * (R + 1) * Emax R (2 * X1 + 2 * R) ^ 2 ≤ 6 * R * (KE ^ 2 * u ^ (332 : ℕ)) := e1
      _ ≤ 6 * R * (KE ^ 2 * ((175 * A / 18) ^ A * (Y ^ 2 * Real.log Y ^ (-A)))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hlp (sq_nonneg _)
      _ = _ := by ring
  have e : (6 * K1 + 6 * KE ^ 2 * (175 * A / 18) ^ A) * R * Y ^ 2 * Real.log Y ^ (-A) =
      6 * (K1 * (R * Y ^ 2 * Real.log Y ^ (-A))) +
        6 * KE ^ 2 * (175 * A / 18) ^ A * (R * Y ^ 2 * Real.log Y ^ (-A)) := by ring
  rw [e]
  linarith
/-! ## Part 8. Theorem 5 and the F-0008 repair from PP1993 -/
end LeanLab.Halupczok2012
