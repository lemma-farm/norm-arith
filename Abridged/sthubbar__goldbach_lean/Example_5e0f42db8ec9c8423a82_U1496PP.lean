module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v6400253cb469.LeanLab.Halupczok2012.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v6400253cb469.LeanLab.Halupczok2012.U1439Thm2Reduction ====
public section
/-!
# P0077 Halupczok 2012, Theorem 2 reduced to Theorem 5 and the main term step, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper proves Theorem 2 by writing the ternary sum as `∑_{p₁} log p₁ · binSum(n - p₁)` and
splitting `binSum(n - p₁) - T(n,q,a) Y₁ Y₂ / …` into

* the BINARY PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ (binSum(n - p₁) - 𝔖(n - p₁) Y₂)|`, bounded from
  the Perelli-Pintz mean square, the paper's Theorem 5, and its Lemma 1; and
* the MAIN TERM PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ 𝔖(n - p₁) - 𝔗(n,q,a) Y₁|`, bounded from the
  Perelli-Pintz-Salerno short interval Bombieri-Vinogradov theorem, the paper's Theorem 3, and
  the singular series computation with the Chinese remainder theorem.

Here:

* `binaryPart`: the binary part is `≪ Y₁ Y₂ L^{-A}`. PROVED CONDITIONAL ON `Theorem5` only.
  The paper's Lemma 1 is NOT needed: in Theorem 2, `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives `Q² ≪ Y₁`,
  so the elementary divisor moment `divisor_moment` and Cauchy-Schwarz suffice.
* `theorem2_of_inputs : Theorem5 → MainTermMV → Theorem2`. CONDITIONAL ON both.
* `theorem2Zeroed_of_inputs`: the F-0008 repair, the all-`q` form with `T0`, CONDITIONAL ON the
  same two inputs instead of the paper's Theorem 2.

`MainTermMV` is still the paper's own main term step, its displays after (10); its standard
input is `Theorem3`, Perelli-Pintz-Salerno, stated below; `U1457SingSeries` derives
`MainTermMV` from `Theorem3` and the singular series facts proved in `U1462Tails`.
The lab's `PNTPort.BV.BombieriVinogradov` is for `ψ(x; q, a)` over `[1, x]`; it does not give
intervals of length `Y₁ = X₁^{3/5+ε}`, so it cannot replace `Theorem3`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
/-! ### The cited inputs -/
/-- **Theorem 5 of the paper**, Perelli-Pintz: for `Y^{1/3+ε} ≪ R ≪ Y ≍ 2X₁ - X₂ - Y ≥ 0`,
`R ≤ X₁`, `X₂^{7/12+ε₂} ≪ Y ≤ X₂`,
`∑_{k ∈ [X₁, X₁+R]} |∑_{p₂+p₃=2k, p₂ ∈ [X₂,X₂+Y]} log p₂ log p₃ - 𝔖(2k) Y|² ≪ R Y² L^{-A}`,
`L = log Y`. Cited input. -/
def Theorem5 : Prop :=
  ∀ A ε ε2 : ℝ, 0 < A → 0 < ε → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y →
    c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 → c2 * Y ^ (1 / 3 + ε) ≤ R → R ≤ c3 * Y → R ≤ X1 →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      C * R * Y ^ 2 * Real.log Y ^ (-A)

end LeanLab.Halupczok2012

end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_5e0f42db8ec9c8423a82_U1496PP ====
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

/-! ## Part 7. Asymptotics on one window of the minimal scale -/

/-! ## Part 8. Theorem 5 and the F-0008 repair from PP1993 -/
set_option linter.unusedVariables false in
/-- **`Theorem5` from the Goldbach analogue of PP1993 Theorem 3.** CONDITIONAL ON
`PP1993Goldbach` only. Each window is cut into pieces of length `≍ (c₄ Y)^{1/3+δ}`,
`δ = min(ε, ε₂, 1/12)/2`, and `piece` is applied to each. -/
theorem theorem5_of_PP (hPP : PP1993Goldbach) 
    (h_LeanLab_Halupczok2012_sum_kRange_le_pieces : ∀ (X R : ℝ),
      0 < R →
        ∀ (m : ℕ),
          0 < m →
            ∀ (g : ℕ → ℝ),
              (∀ (k : ℕ), 0 ≤ g k) →
                ∑ k ∈ LeanLab.Halupczok2012.kRange X R, g k ≤
                  ∑ j ∈ Finset.range m,
                    ∑ k ∈ LeanLab.Halupczok2012.kRange (X + (↑j : ℝ) * (R / (↑m : ℝ))) (R / (↑m : ℝ)),
                      g k)
    (h_LeanLab_Halupczok2012_floor_pieces : ∀ {R R0 : ℝ},
      0 < R0 → R0 ≤ R → 1 ≤ ⌊R / R0⌋₊ ∧ R0 ≤ R / (↑⌊R / R0⌋₊ : ℝ) ∧ R / (↑⌊R / R0⌋₊ : ℝ) ≤ 2 * R0)
    (h_LeanLab_Halupczok2012_piece : LeanLab.Halupczok2012.PP1993Goldbach →
      ∀ {A ε2 δ : ℝ},
        0 < A →
          0 < ε2 →
            0 < δ →
              δ ≤ ε2 / 2 →
                δ ≤ 1 / 24 →
                  ∀ {c1 c4 c5 : ℝ},
                    0 < c1 →
                      0 < c4 →
                        0 < c5 →
                          ∃ (C : ℝ) (Y0 : ℝ),
                            ∀ (X1 X2 Y R : ℝ),
                              Y0 ≤ Y →
                                c1 * X2 ^ (7 / 12 + ε2) ≤ Y →
                                  Y ≤ X2 →
                                    c4 * Y ≤ 2 * X1 - X2 - Y →
                                      2 * X1 - X2 - Y ≤ c5 * Y →
                                        (c4 * Y) ^ (1 / 3 + δ) / 4 ≤ R →
                                          R ≤ (c4 * Y) ^ (1 / 3 + δ) / 2 →
                                            ∑ k ∈ LeanLab.Halupczok2012.kRange X1 R,
                                                (LeanLab.Halupczok2012.binSum X2 Y (2 * k) -
                                                    LeanLab.Halupczok2012.S (2 * k) * Y) ^
                                                  2 ≤
                                              C * R * Y ^ 2 * Real.log Y ^ (-A))
    : Theorem5 := by
  intro A ε ε2 hA hε hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  set δ : ℝ := min (min ε ε2) (1 / 12) / 2 with hδ
  have hm1 := min_le_left (min ε ε2) (1 / 12)
  have hm2 := min_le_right (min ε ε2) (1 / 12)
  have hm3 := min_le_left ε ε2
  have hm4 := min_le_right ε ε2
  have hδ0 : 0 < δ := by
    rw [hδ]; have : 0 < min (min ε ε2) (1 / 12) := lt_min (lt_min hε hε2) (by norm_num)
    linarith
  have hδε : δ ≤ ε / 2 := by rw [hδ]; linarith
  have hδ2 : δ ≤ ε2 / 2 := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; linarith
  obtain ⟨C, Y0, hC⟩ := h_LeanLab_Halupczok2012_piece hPP hA hε2 hδ0 hδ2 hδ1 hc1 hc4
    (show 0 < c5 + 2 * c3 by positivity)
  set a : ℝ := 1 / 3 + δ with ha
  set K : ℝ := c4 ^ a / (4 * c2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C, max (max Y0 1) (K ^ (2 / ε)), ?_⟩
  intro X1 X2 Y R hY h1 h2 h3 h4 h5 h6 h7 h8
  have hY0 : Y0 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY1 : 1 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYK : K ^ (2 / ε) ≤ Y := le_trans (le_max_right _ _) hY
  set R0 := (c4 * Y) ^ a / 4 with hR0def
  have hR0 : 0 < R0 := by
    rw [hR0def]; have : 0 < (c4 * Y) ^ a := Real.rpow_pos_of_pos (by positivity) _
    linarith
  have hR0R : R0 ≤ R := by
    have e1 : (c4 * Y) ^ a = c4 ^ a * Y ^ a := Real.mul_rpow hc4.le (by linarith)
    have e2 : K ≤ Y ^ (ε / 2) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hYK (by positivity : 0 ≤ ε / 2)
      rwa [← Real.rpow_mul hK0, show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one] at this
    have e3 : Y ^ (ε / 2) * Y ^ a ≤ Y ^ (1 / 3 + ε) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by rw [ha]; linarith)
    have e4 : c4 ^ a = 4 * c2 * K := by rw [hK]; field_simp
    have hYa : 0 ≤ Y ^ a := by positivity
    calc R0 = c2 * (K * Y ^ a) := by rw [hR0def, e1, e4]; ring
      _ ≤ c2 * (Y ^ (ε / 2) * Y ^ a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 hYa) hc2.le
      _ ≤ c2 * Y ^ (1 / 3 + ε) := mul_le_mul_of_nonneg_left e3 hc2.le
      _ ≤ R := h3
  obtain ⟨hm1, hlo, hhi⟩ := h_LeanLab_Halupczok2012_floor_pieces hR0 hR0R
  set m := ⌊R / R0⌋₊ with hmdef
  have hm0 : 0 < m := hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hRpos : 0 < R := lt_of_lt_of_le hR0 hR0R
  set g : ℕ → ℝ := fun k => (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 with hg
  have hgnn : ∀ k, 0 ≤ g k := fun k => sq_nonneg _
  have hpiece : ∀ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k ≤
      C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := by
    intro j hj
    have hj' : (j : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjR : (j : ℝ) * (R / m) ≤ R := by
      rw [mul_div_assoc']; rw [div_le_iff₀ hmR]; nlinarith
    have hjR0 : 0 ≤ (j : ℝ) * (R / m) := by positivity
    exact hC (X1 + j * (R / m)) X2 Y (R / m) hY0 h1 h2 (by linarith) (by nlinarith)
      (by rw [hR0def] at hlo; exact hlo) (by rw [hR0def] at hhi; linarith)
  calc ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2
      = ∑ k ∈ kRange X1 R, g k := rfl
    _ ≤ ∑ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k :=
        h_LeanLab_Halupczok2012_sum_kRange_le_pieces X1 R hRpos m hm0 g hgnn
    _ ≤ ∑ j ∈ range m, C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := Finset.sum_le_sum hpiece
    _ = C * R * Y ^ 2 * Real.log Y ^ (-A) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
end LeanLab.Halupczok2012
