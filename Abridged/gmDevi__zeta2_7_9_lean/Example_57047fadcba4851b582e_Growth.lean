import Mathlib

-- ==== Examples.gmDevi__zeta2_7_9_lean.Dependencies.vd9600a014307.Zeta2Lean.Pair.Defs ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Zeta2Lean.Pair.Defs — definitions for the pair `{ζ₂(7), ζ₂(9)}`

Target: **at least one of `ζ₂(7)`, `ζ₂(9)` is irrational** (map of statements: `BLUEPRINT_PAIR.md`).
This file only adds the *pair-specific* objects.  The Volkenborn infrastructure (`volkenbornSum`,
`HasVolkenborn`, `volkenborn`, `halfPow`, `J`, `zeta2`, `Ahalf`, `dn`, the `HasVolkenborn` API) is
reused from `Zeta2Lean/Defs.lean` (namespace `Zeta2`).  Everything here lives in the namespace
`Zeta2.Pair`; inside it, short names such as `rcoef`, `rho0`, `Z7` refer to the pair versions
(Lean resolves the innermost namespace first), outside write `Pair.rcoef` etc.

## The family (shifted well-poised / Rhin–Viola-type deformation of the LSZ half-shift family)

For `n : ℕ` and a shift vector `h : Fin 6 → ℤ`,
```
R_n(t) = (2t + n) · ∏_{m<6} (t + 1/2 - h_m)_{n + 2 h_m} / (t)_{n+1}^6 ,
(t + 1/2 - h)_{n+2h} = ∏_{u ∈ [-h, n+h)} (t + 1/2 + u)          (offsets n h),
```
with `h` **admissible** (`Admissible n h`): `∑ h_m = 0`, every length `n + 2h_m ≥ 0`, and at least
`j + 2 = 5` of the `h_m` are `≥ 0` (the critical-zero condition used by the denominator argument).
Then `deg R_n = 1 + 6n - 6(n+1) = -5`, the poles are `t = 0, -1, …, -n` (order `≤ 6`) and
`R_n(-t-n) = -R_n(t)`.  **No power of 2 is built in** (unlike the `{7,9,11}` project, which uses
`2^{16n}`): all numerical data of the exploration are in this unnormalised form.  Powers of 2 are
neutral for the criterion (`|a|_∞ · |L|_2` is invariant); the assembly therefore bounds the *odd
part* `D · ‖D‖₂` of the common denominator.

Partial fractions: `R_n(t) = ∑_{i=1}^{6} ∑_{k=0}^{n} r_{i,k} (t+k)^{-i}` with the explicit Taylor
formula `r_{6-μ,k} = [ε^μ] G_k(ε)`, `G_k(ε) = ε^6 R_n(-k+ε)`:
```
G_k(ε) = (n - 2k + 2ε) · ∏_m ∏_{u ∈ [-h_m, n+h_m)} (u - k + 1/2 + ε)
                       · ∏_{j ≤ n, j ≠ k} (j - k + ε)^{-6}
```
computed in `PowerSeries ℚ` (the inverted product has non-zero constant term, so `⁻¹` is the honest
inverse).  `Stmt_PF` links these coefficients with the product form of `R_n`.

The linear form: `S_n = -∫_{ℤ₂} R_n'''(t + 1/2) dt = ∫ integrand`, with
`integrand n h x = ∑_{i,k} (i)₃ r_{i,k} (x + k + 1/2)^{-i-3}`, and (`Stmt_L1`)
```
S_n = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9),
Z₇ = (3)₄ 2^7 c₃ = 46080 c₃,  Z₉ = (5)₄ 2^9 c₅ = 860160 c₅,
```
(`c₁ = 0` by degree, `c₂ = c₄ = c₆ = 0` by the parity lemma).  The exploration's `lfam.py` uses
`S = +∫ R''' (t+1/2) dt`, so its `(rho0, C[6], C[8])` are `-(ρ₀, Z₇, Z₉)` here.

The linear-form machinery is stated **generically** (`genIntegrand`, `genRho0`, `genCsum` for an
arbitrary coefficient array `r : ℕ → ℕ → ℚ` and pole order `a`), so that its proof
(`Stmt_GenLinearForm`) is independent of the family and could be reused for other
configurations/families.

## Configurations

A `Config` is a sequence of degrees `cfg.n m → ∞` with admissible shift vectors `cfg.h m`.
Configuration **E** (the numerically best pair configuration): `h/n = (-0.425, 0.025, 0.05, 0.075,
0.125, 0.15)`, i.e. `n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)` (`configE`).

## Target constants

`gE = -0.72` (coefficient growth, measured `≈ -0.79`) and `deltaE = 9` (log of the odd part of the
provable common denominator per `n`, estimated `10 - R_∞ ≈ 8.91`); `gE + deltaE = 8.28 < 12 log 2 =
8.3178` (`marginE`, in `Pair/Assembly.lean`).  The main theorem is also available for arbitrary
`(g, δ)` with `g + δ < 12 log 2` (`Pair/Main.lean`).
-/
set_option linter.style.longLine false
open Filter Topology Finset PowerSeries
noncomputable section
namespace Zeta2.Pair
/-! ## Shift vectors -/
/-- Admissible shift vector `h` for degree `n`: `∑_m h_m = 0`, all lengths `n + 2 h_m ≥ 0`, and at
least five of the six shifts are `≥ 0` (critical-zero condition: every factor with `h_m ≥ 0` has
offsets `[-h_m, n + h_m) ⊇ [0, n)`, so `R_n` vanishes to order `≥ 5 = j + 2` at every critical
point `-1/2 - c`, `0 ≤ c < n`). -/
def Admissible (n : ℕ) (h : Fin 6 → ℤ) : Prop :=
  ∑ m, h m = 0 ∧ (∀ m, 0 ≤ (n : ℤ) + 2 * h m) ∧ 5 ≤ (univ.filter fun m => 0 ≤ h m).card
/-- The offsets `u ∈ [-h, n+h)` of the numerator factor
`(t + 1/2 - h)_{n+2h} = ∏_{u ∈ [-h, n+h)} (t + 1/2 + u)`. -/
def offsets (n : ℕ) (h : ℤ) : Finset ℤ :=
  Ico (-h) ((n : ℤ) + h)
/-- Taylor expansion `ε ↦ ∏_m (y + ε + 1/2 - h_m)_{n + 2h_m}` of the numerator at `t = y`. -/
def numSer (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ) : PowerSeries ℚ :=
  ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (C (y + 1 / 2 + (u : ℚ)) + X)
/-- `G_k(ε) = ε^6 R_n(-k+ε) = (n - 2k + 2ε) · numSer n h (-k) · ∏_{j ≤ n, j ≠ k} (j - k + ε)^{-6}`.
-/
def Gser (n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) : PowerSeries ℚ :=
  (C ((n : ℚ) - 2 * k) + C 2 * X) * numSer n h (-(k : ℚ)) *
    (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹
/-- Partial-fraction coefficient `r_{i,k}` of `R_n` (`1 ≤ i ≤ 6`, `0 ≤ k ≤ n`), `0` otherwise:
`r_{6-μ,k} = [ε^μ] G_k(ε)`. -/
def rcoef (n : ℕ) (h : Fin 6 → ℤ) (i k : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ 6 ∧ k ≤ n then coeff (6 - i) (Gser n h k) else 0
/-! ## Generic linear forms (any coefficient array `r`, any pole order `a`) -/
def genCsum (n : ℕ) (r : ℕ → ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), r i k

/-! ## The linear form of the pair family -/
/-- `c_i = ∑_k r_{i,k}` for the pair family. -/
def csum (n : ℕ) (h : Fin 6 → ℤ) (i : ℕ) : ℚ :=
  genCsum n (rcoef n h) i

/-! ## Denominators -/

/-- Shift pattern of configuration E in units of `n/40`: `(-17, 1, 2, 3, 5, 6)`. -/
def hE : Fin 6 → ℤ :=
  ![-17, 1, 2, 3, 5, 6]

end Zeta2.Pair
end

end

-- ==== Examples.gmDevi__zeta2_7_9_lean.Dependencies.vd9600a014307.Zeta2Lean.Pair.Statements ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Zeta2Lean.Pair.Statements — one `Prop` per lemma of the pair blueprint

Every lemma of the pair proof is a `def Stmt_X : Prop` (or a `structure Stmt_X : Prop` with named
fields), in the namespace `Zeta2.Pair`.  Proof files `Zeta2Lean/Pair/Proofs/*.lean` prove them,
taking the statements they depend on as *hypotheses*; `Zeta2Lean/Pair/Assembly.lean` derives the
main theorem (complete, no gaps); `Zeta2Lean/Pair/Main.lean` wires everything together.

Reused from the `{7,9,11}` repository (namespace `Zeta2`, file `Zeta2Lean/Statements.lean`):
`PNT_Stmt` (proved in `Zeta2Lean/Cited/PNT.lean`), `Stmt_JConv`, `Stmt_Translation`,
`Stmt_Criterion`, `Stmt_Delta`, `Stmt_DeltaFun` and their proof files
`Zeta2Lean/Proofs/{JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions}.lean`.

Kinds of statements here (all are proved):
* **routine** (proof files with `gap = ''`): `Stmt_GenLinearForm`, `Stmt_PF`, `Stmt_CoeffVanish`,
  `Stmt_L1`, `Stmt_IntegrandTaylor`, `Stmt_CrudeInt`, and `Stmt_Valuation` (GAP 4: the Lai/Sprang
  Δ-calculus bound).  `Pair/Main.lean` uses their proofs.
* **the three gap statements** `Stmt_Growth` (GAP 1), `Stmt_Denominators` (GAP 2),
  `Stmt_Nonvanishing` (GAP 3), proved for configuration E in `Pair/Proofs/Growth.lean`,
  `Denominators.lean` and `Nonvanishing.lean`.  They are parametrised by a configuration
  `cfg : Config` and by the rates `g`, `δ`, and stated in exactly the form `main_of_stmts`
  consumes; the margin condition is `g + δ < 12 log 2`.

Normalisation reminder: `R_n` carries **no** power of `2`; `ρ₀, Z₇, Z₉` have 2-adic denominators of
size `≈ 2^{12n}`, `v₂(S_n) ≈ 12 n`, and only the *odd part* `D · ‖D‖₂` of a common denominator `D`
enters the margin.
-/
set_option linter.style.longLine false
open Filter Topology Finset PowerSeries
noncomputable section
namespace Zeta2.Pair
/-! ## The main statement -/

/-- **Parity lemma and vanishing sums**: `r_{i,n-k} = (-1)^{i+1} r_{i,k}`
(from `R_n(-t-n) = -R_n(t)`;
each shifted factor `(t+1/2-h)_{n+2h}` is individually symmetric), `c₁ = 0` (`deg R_n = -5`) and
`c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i k : ℕ, k ≤ n →
    rcoef n h i (n - k) = (-1) ^ (i + 1) * rcoef n h i k
  c1 : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → csum n h 1 = 0
  ceven : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i : ℕ, Even i → csum n h i = 0

end Zeta2.Pair
end

end

-- ==== Examples.gmDevi__zeta2_7_9_lean.Examples.Example_57047fadcba4851b582e_Growth ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# GAP 1 (growth): exponential decay of `ρ₀, Z₇, Z₉` for configuration E

gap: 'growth'.  **Task.** `Stmt_Growth configE gE`: for every `ε > 0`, eventually in `m`
(`n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)`), `|ρ₀|, |Z₇|, |Z₉| ≤ exp((-0.72 + ε) n)`.

## Proof as formalized (`docs/proof.md` §6, contour integrals with half-integer kernels)

The proof is complete.  The "computer-assisted" part of the informal proof, two
explicit numerical inequalities for the landscape function (`GrowthAux.landscape_real`,
`GrowthAux.landscape_vert`), is a kernel-checked certified subdivision in
`Pair/Proofs/Landscape/` (see the end of this docstring).

1. **Kernels** (`kerS s t = ∑_{ν ∈ ℤ} (t - ν - 1/2)^{-s}`, `s ≥ 2`): holomorphic off the
   half-integers, bounded on vertical lines through integers, and `O(e^{-2π Im t})` for
   `Im t ≥ 1` (`kerS_decay`, via the Eisenstein `q`-expansion identity).
   (They replace `(π sec πt)²`, `(π sec πt)⁴`, `(π tan πt)''''` of the informal proof.)
2. **Vertical-line representation** (`vline_Pc_kerS`): for the line `Re t = m = n/40`,
   `∫ R_n(m+iy) K_s(m+iy) dy = -2π ∑_{l ≥ 0} D_{s-1}(m + l + 1/2)` (`D_j` = `j`-th Taylor
   coefficient of `R_n`), by Cauchy's formula on right half-planes (`vline_higher`,
   `vline_left`, derived from `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) and
   dominated interchange of `∑_ν` and `∫`.  With the critical zeros (`Dc_hpt_eq_zero`: `R_n`
   vanishes to order `≥ 5` at the half-integers in `(-n - n/40, n/40)`), the symmetry
   `R_n(-n-t) = -R_n(t)` and `c₁ = c₂ = c₄ = c₆ = 0` this gives (`Iker_two/four/five`)
   `I₂ = π (3 c₃ Z₄ + 5 c₅ Z₆)`, `I₄ = π (10 c₃ Z₆ + 35 c₅ Z₈)`,
   `I₅ = -2π (15 c₃ Z⁺₇ + 70 c₅ Z⁺₉ + ρ₀/24)` (`Z_s = ∑_{ν∈ℤ} (ν+1/2)^{-s}`,
   `Z⁺_s = ∑_{l≥0} (l+1/2)^{-s}`).  The determinant `105 Z₄ Z₈ - 50 Z₆²` is `> 0` by
   Cauchy–Schwarz (`det_pos`), hence `|ρ₀|, |Z₇|, |Z₉| ≤ K (|I₂| + |I₄| + |I₅|)`
   (`coeff_le_Iker`).
3. **Contour** (`Iker_le`): by conjugation symmetry only the upper half-line matters; it is cut at
   height `1`, and the part above height `1` is shifted from `Re t = m` to `Re t = 0.07 n`
   (`halfstrip_shift`).  Pieces: A (`m + iy`, `0 ≤ y ≤ 1`: comparison with `m + i`,
   `norm_Rc_vert_le`), B (`x + i`, `m ≤ x ≤ 0.07 n`), C₁ (`0.07 n + iy`, `1 ≤ y ≤ n`),
   C₂ (`y ≥ n`).
4. **Pointwise bound** (`norm_Rc_le`, window comparison of `∑ log|t + j|` with integrals):
   `|R_n(t)| ≤ |2t + n| (|t| + 2n)^6 exp(n Φ(t/n))` for `Re t ≥ 0`, `Im t ≥ 1`, where
   `Φ(x, y) = PhiE x y = ∑_p [G(x+1+η_p, y) - G(x-η_p, y)] - 6 [G(x+1, y) - G(x, y)]`,
   `G(a, y) = (a/2) log(a² + y²) + y arctan(a/y) - a` (`Gf`), i.e. `Φ = Re φ` of the informal
   proof.  Analytic landscape facts (proved): `Φ(ξ, η) ≤ Φ(ξ, 0) + 6πη` (`PhiE_le_add`,
   `∂_η Φ ≤ 6π`) and `Φ(ξ, η) ≤ 4` for `η ≥ 1` (`PhiE_le_four`, second-order Taylor).
5. **Result**: `|I_s| ≤ C m⁸ e^{-0.72 · 40 m}` (`Iker_le`), hence the statement
   (`growth_main`).  (The informal proof's sharp rate `-0.78127` is not needed: the contour only
   has to stay below the target `gE = -0.72`.)

## The two numerical landscape inequalities (certified in `Pair/Proofs/Landscape/`)

* `landscape_real : ∀ ξ ∈ [1/40, 7/100], PhiE ξ 0 ≤ -18/25` — the real profile
  `P(ξ) = ∑_j s_j (ξ + a_j) log|ξ + a_j|` (only logarithms); true maximum `-0.80049` (at
  `ξ ≈ 0.02503`), margin `0.08`.  `Landscape.Preal_le` (`RealProfile.lean`): nine cells with
  endpoints in `(1/2000) ℤ`; every summand `s_j x log x` is monotone on each cell, so it is
  bounded by its value at an endpoint.
* `landscape_vert : ∀ η ∈ (0, 1], PhiE (7/100) η - 2πη ≤ -18/25` — the vertical line through
  the saddle point `τ* = 0.06959 + 0.03128 i` (logarithms and arctangents); true maximum
  `-0.78127` (at `η ≈ 0.031`), margin `0.061`.  `Landscape.Psi_le` (`VertLine.lean`): four cells
  `[0, 1/50, 1/20, 9/50, 1]`, on each `Ψ(η) ≤ Ψ(l) + (r - l) sup Ψ'` (mean value theorem), the
  sup from the monotonicity of each summand `s_j arctan(a_j/ζ)` of `Ψ'`.

Values of `log` and `arctan` at the rational grid points are certified by `Landscape/Numerics.lean`
(`artanh` series with geometric tail after reduction by powers of `2`, `Real.log_two_gt_d9`;
alternating Taylor polynomials of degree 15/17 after reduction by `π/4`, `π/2`;
`Real.pi_gt_d20`); every side condition is a closed rational inequality checked by `norm_num`.
The certificate files were generated by `Landscape/gen/lean_real.py`, `Landscape/gen/lean_vert.py`
(exact `Fraction` arithmetic).  This replaces the interval-arithmetic certification of Lemma 7
of `docs/proof.md` §6.4 (Python scripts of the research session, not part of this repository).
-/
set_option linter.style.longLine false
open Complex MeasureTheory Filter Topology Set Finset PowerSeries
open scoped Real
noncomputable section
namespace Zeta2.Pair
namespace GrowthAux
-- (part: growth_base)
/-! ## Vertical-line integrals -/

/-! ## Half-integer kernels -/
/-- The half-integer points `x_ν = ν + 1/2`. -/
def hpt (ν : ℤ) : ℂ := (ν : ℂ) + 1 / 2
/-- The kernel `K_s(t) = ∑_{ν ∈ ℤ} (t - (ν + 1/2))^{-s}`. -/
def kerS (s : ℕ) (t : ℂ) : ℂ := ∑' ν : ℤ, ((t - hpt ν) ^ s)⁻¹

/-! ## Pair algebra -/

/-- The partial-fraction form `∑_{i,k} r_{i,k} (t+k)^{-i}` of `R_n`. -/
def Pc (n : ℕ) (h : Fin 6 → ℤ) (t : ℂ) : ℂ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1), (rcoef n h i k : ℂ) * ((t + k) ^ i)⁻¹

/-! ### Bounds on `Pc` -/
def M2 (n : ℕ) (h : Fin 6 → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1), ‖(rcoef n h i k : ℂ)‖ * (1 + k)

/-! ### Taylor coefficients at the critical half-integers -/

/-! ### Sums over the half-integers -/

-- (part: growth_pw)
/-! ## The primitive `Gf` -/

-- (part: growth_rep)
/-! ## `Pc` along vertical lines -/

/-! ## The three kernel integrals of configuration E -/

/-! ## Cauchy–Schwarz for the half-integer zeta values -/

-- (part: growth_land)
/-! ## Derivative and continuity in `y` -/

/-! ## The bound for large `y` (second-order Taylor in the first variable) -/

/-! ## The numerical landscape inequalities (certificate)

The certified subdivision arguments live in `Pair/Proofs/Landscape/` (`RealProfile.lean`,
`VertLine.lean`), stated for explicit elementary functions (`Landscape.Preal`, `Landscape.Psi`,
with `Landscape.Lf` a verbatim copy of `Gf`); here they are identified with `PhiE`. -/

-- (part: growth_contour)
/-! ## Elementary norm comparisons -/

/-! ## Pointwise bounds on the contour pieces -/

/-! ## The contour integrand and its integrability -/
/-- The contour integrand `f_s = R_n · K_s` for configuration E. -/
def fs (m s : ℕ) (t : ℂ) : ℂ := Pc (40 * m) (fun p => (m : ℤ) * hE p) t * kerS s t


set_option linter.unusedVariables false in
theorem fs_top_tendsto (hV : Stmt_CoeffVanish) (m : ℕ) {s : ℕ} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) 
    (h_Zeta2_Pair_GrowthAux_M2_nonneg : ∀ (n : ℕ) (h : Fin 6 → ℤ), 0 ≤ Zeta2.Pair.GrowthAux.M2 n h)
    (h_Zeta2_Pair_GrowthAux_norm_fs_le_decay : Zeta2.Pair.Stmt_CoeffVanish →
      ∀ (m : ℕ) {s : ℕ} {κ : ℝ},
        0 ≤ κ →
          (∀ (t : ℂ), 1 ≤ t.im → ‖Zeta2.Pair.GrowthAux.kerS s t‖ ≤ κ * Real.exp (-2 * Real.pi * t.im)) →
            ∀ {t : ℂ},
              0 ≤ t.re →
                1 ≤ t.im →
                  ‖Zeta2.Pair.GrowthAux.fs m s t‖ ≤
                    (κ *
                        Zeta2.Pair.GrowthAux.M2 (40 * m) fun (p : Fin 6) ↦ (↑m : ℤ) * Zeta2.Pair.hE p) /
                      t.im ^ 2)
    :
    Tendsto (fun Y : ℝ => ∫ x in a..b, fs m s (x + Y * I)) atTop (𝓝 0) := by
  set M := M2 (40 * m) (fun p => (m : ℤ) * hE p)
  have hM : 0 ≤ M := h_Zeta2_Pair_GrowthAux_M2_nonneg _ _
  have hlim : Tendsto (fun Y : ℝ => κ * M * |b - a| / Y ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  have hbound : ∀ x ∈ Set.uIoc a b, ‖fs m s (x + Y * I)‖ ≤ κ * M / Y ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have h := h_Zeta2_Pair_GrowthAux_norm_fs_le_decay hV m hκ0 hκ (t := (x : ℂ) + Y * I) (by simp; linarith [hx.1])
      (by simp; exact hY)
    simpa using h
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) (le_of_eq ?_)
  ring

/-! ## The bound on `I_s` -/

-- (part: growth_final)
/-! ## Assembly: `Stmt_Growth configE gE` -/

end GrowthAux
end Zeta2.Pair
end
