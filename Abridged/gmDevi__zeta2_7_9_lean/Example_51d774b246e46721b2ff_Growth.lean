import Mathlib

-- ==== Examples.gmDevi__zeta2_7_9_lean.Dependencies.vd9600a014307.Zeta2Lean.Defs ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Zeta2Lean.Defs — the Volkenborn integral, the 2-adic zeta values and the Δ-calculus

The shared definitions of the development.  They come from the `{7,9,11}` repository
(https://github.com/gmDevi/zeta2-7-9-11-lean, file of the same name); the definitions of that
project's construction, which the pair does not use, are omitted here.  The pair construction is
in `Zeta2Lean/Pair/Defs.lean`.  "proof.md" is the informal proof `docs/proof.md`.

* The first six definitions, `volkenbornSum`, `HasVolkenborn`, `volkenborn`, `halfPow`, `J` and
  `zeta2`, are the **trusted definitions**: they are the only project definitions in the statement
  of the main theorem, and `Challenge.lean` contains verbatim copies of them.  They are identical
  to those of the `{7,9,11}` repository.
* `Ahalf` and `dn` are used by the pair's linear form and denominators.
* `DeltaGe`, `DeltaAll`, `IntValued` and `hcoef` are the objects of the 2-adic Δ-calculus
  (`Stmt_Delta`, `Stmt_DeltaFun` in `Zeta2Lean/Statements.lean`).
* The file ends with the basic API of the Volkenborn Riemann sums.

Conventions.
* `ℚ_[2]` is Mathlib's field of 2-adic numbers; `‖·‖` its norm (`‖2‖ = 1/2`).
* The Volkenborn integral (proof.md P1) is *not* in Mathlib.  We use Riemann sums
  `volkenbornSum f N = 2^{-N} ∑_{x<2^N} f x` and the predicate `HasVolkenborn f I`
  (`volkenbornSum f N → I`).  `volkenborn f = limUnder …` is only a name for the limit; every
  statement that uses a value comes with a `HasVolkenborn` certificate.
* `J s = ∫_{ℤ₂} (t+1/2)^{-s} dt` and `zeta2 s = J (s-1) / ((s-1) 2^s)`.  The identification of
  `zeta2 s` with the Kubota–Leopoldt value `L₂(s, ω^{1-s})` is LSZ Lemma 2.8 (cited, not
  formalised).  Irrationality is invariant under the non-zero rational factor `(s-1) 2^s`, so the
  theorem about `J 6` and `J 8` *is* the theorem about `ζ₂(7)` and `ζ₂(9)`.
-/
set_option linter.style.longLine false
open Filter Topology Finset PowerSeries
noncomputable section
namespace Zeta2
/-! ## Volkenborn integral via Riemann sums (proof.md P1, P2) -/

def Ahalf (k s : ℕ) : ℚ :=
  ∑ l ∈ range k, (((l : ℚ) + 1 / 2)⁻¹) ^ s

/-! ## Basic API (proved here, available to every proof file) -/

end Zeta2
end

end

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
/-- `ρ₀ = -∑_{i=1}^{a} ∑_{k=0}^{n} (i)₄ r_{i,k} A_k^{(i+4)}`, `A_k^{(s)} = ∑_{ℓ<k} (ℓ+1/2)^{-s}`
(`Zeta2.Ahalf`). -/
def genRho0 (a n : ℕ) (r : ℕ → ℕ → ℚ) : ℚ :=
  -∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
      ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * r i k * Ahalf k (i + 4)
/-! ## The linear form of the pair family -/
/-- `c_i = ∑_k r_{i,k}` for the pair family. -/
def csum (n : ℕ) (h : Fin 6 → ℤ) (i : ℕ) : ℚ :=
  genCsum n (rcoef n h) i
/-- The rational part `ρ₀` of `S_n`. -/
def rho0 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  genRho0 6 n (rcoef n h)
/-- `Z₇ = (3)₄ 2^7 c₃ = 46080 c₃`, the coefficient of `ζ₂(7)`. -/
def Z7 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  46080 * csum n h 3
/-- `Z₉ = (5)₄ 2^9 c₅ = 860160 c₅`, the coefficient of `ζ₂(9)`. -/
def Z9 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  860160 * csum n h 5
def Rnum (n : ℕ) (h : Fin 6 → ℤ) : Polynomial ℚ :=
  (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ)) *
    ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))
/-- `(t)_{n+1}^6 · ∑_{i,k} r_{i,k} (t+k)^{-i}` as a polynomial in `t`. -/
def PFpoly (n : ℕ) (h : Fin 6 → ℤ) : Polynomial ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1),
    Polynomial.C (rcoef n h i k) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (6 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 6
/-- The Taylor expansion `ε ↦ R_n(y + ε)` (meaningful when `y ∉ {0, -1, …, -n}`). -/
def Rser (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ) : PowerSeries ℚ :=
  (C (2 * y + n) + C 2 * X) * numSer n h y * ((∏ j ∈ range (n + 1), (C (y + j) + X)) ^ 6)⁻¹
/-! ## Denominators -/
structure Config where
  /-- the degree at step `m` -/
  n : ℕ → ℕ
  /-- the shift vector at step `m` -/
  h : ℕ → Fin 6 → ℤ
  adm : ∀ m, Admissible (n m) (h m)
  tendsto : Tendsto n atTop atTop
/-- Shift pattern of configuration E in units of `n/40`: `(-17, 1, 2, 3, 5, 6)`. -/
def hE : Fin 6 → ℤ :=
  ![-17, 1, 2, 3, 5, 6]
set_option linter.unusedVariables false in
axiom _root_.Zeta2.Pair.admissible_E : ∀ (m : ℕ), Zeta2.Pair.Admissible (40 * m) fun (i : Fin 6) ↦ (↑m : ℤ) * Zeta2.Pair.hE i
/-- **Configuration E**: `n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)`, i.e.
`h/n = (-0.425, 0.025, 0.05, 0.075, 0.125, 0.15)`. -/
def configE : Config where
  n m := 40 * m
  h m i := (m : ℤ) * hE i
  adm := admissible_E
  tendsto := Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
/-- Target coefficient growth rate for configuration E (measured: `≈ -0.79`). -/
def gE : ℝ :=
  -18 / 25

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
structure Stmt_PF : Prop where
  poly : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → Rnum n h = PFpoly n h
  series : ∀ (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ), Admissible n h → (∀ j ≤ n, y + (j : ℚ) ≠ 0) →
    Rser n h y =
      ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1), C (rcoef n h i k) * ((C (y + k) + X) ^ i)⁻¹
/-- **Parity lemma and vanishing sums**: `r_{i,n-k} = (-1)^{i+1} r_{i,k}`
(from `R_n(-t-n) = -R_n(t)`;
each shifted factor `(t+1/2-h)_{n+2h}` is individually symmetric), `c₁ = 0` (`deg R_n = -5`) and
`c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i k : ℕ, k ≤ n →
    rcoef n h i (n - k) = (-1) ^ (i + 1) * rcoef n h i k
  c1 : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → csum n h 1 = 0
  ceven : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i : ℕ, Even i → csum n h i = 0
def Stmt_Growth (cfg : Config) (g : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
    |(rho0 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z7 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z9 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m)
end Zeta2.Pair
end

end

-- ==== Examples.gmDevi__zeta2_7_9_lean.Examples.Example_51d774b246e46721b2ff_Growth ====
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

/-! ### Taylor coefficients at the critical half-integers -/

/-! ### Sums over the half-integers -/

-- (part: growth_pw)
/-! ## The primitive `Gf` -/

-- (part: growth_rep)
/-! ## `Pc` along vertical lines -/

/-! ## The three kernel integrals of configuration E -/
/-- `I_s(m) = ∫ Pc(m+iy) K_s(m+iy) dy` for configuration E (`n = 40 m`). -/
def Iker (m s : ℕ) : ℂ :=
  ∫ y : ℝ, Pc (40 * m) (fun p => (m : ℤ) * hE p) ((m : ℝ) + y * I) *
    kerS s ((m : ℝ) + y * I)

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

/-! ## The bound on `I_s` -/

-- (part: growth_final)
/-! ## Assembly: `Stmt_Growth configE gE` -/

set_option linter.unusedVariables false in
/-- **GAP 1 for configuration E.** -/
theorem growth_main (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) 
    (h_Zeta2_Pair_GrowthAux_Iker_le : Zeta2.Pair.Stmt_PF →
      Zeta2.Pair.Stmt_CoeffVanish →
        ∀ {s : ℕ},
          2 ≤ s →
            ∃ (C : ℝ),
              0 ≤ C ∧
                ∀ (m : ℕ),
                  1 ≤ m →
                    ‖Zeta2.Pair.GrowthAux.Iker m s‖ ≤
                      C * (↑m : ℝ) ^ 8 * Real.exp (-18 / 25 * (40 * (↑m : ℝ))))
    (h_Zeta2_Pair_configE_n : ∀ (m : ℕ), Zeta2.Pair.configE.n m = 40 * m)
    (h_Zeta2_Pair_GrowthAux_coeff_le_Iker : Zeta2.Pair.Stmt_PF →
      Zeta2.Pair.Stmt_CoeffVanish →
        ∃ (K : ℝ),
          0 ≤ K ∧
            ∀ (m : ℕ),
              1 ≤ m →
                |(↑(Zeta2.Pair.rho0 (40 * m) fun (p : Fin 6) ↦ (↑m : ℤ) * Zeta2.Pair.hE p) : ℝ)| ≤
                    K *
                      (‖Zeta2.Pair.GrowthAux.Iker m 2‖ + ‖Zeta2.Pair.GrowthAux.Iker m 4‖ +
                        ‖Zeta2.Pair.GrowthAux.Iker m 5‖) ∧
                  |(↑(Zeta2.Pair.Z7 (40 * m) fun (p : Fin 6) ↦ (↑m : ℤ) * Zeta2.Pair.hE p) : ℝ)| ≤
                      K *
                        (‖Zeta2.Pair.GrowthAux.Iker m 2‖ + ‖Zeta2.Pair.GrowthAux.Iker m 4‖ +
                          ‖Zeta2.Pair.GrowthAux.Iker m 5‖) ∧
                    |(↑(Zeta2.Pair.Z9 (40 * m) fun (p : Fin 6) ↦ (↑m : ℤ) * Zeta2.Pair.hE p) : ℝ)| ≤
                      K *
                        (‖Zeta2.Pair.GrowthAux.Iker m 2‖ + ‖Zeta2.Pair.GrowthAux.Iker m 4‖ +
                          ‖Zeta2.Pair.GrowthAux.Iker m 5‖))
    (h_Zeta2_Pair_GrowthAux_eventually_poly_le_exp : ∀ (A : ℝ) {δ : ℝ}, 0 < δ → ∀ᶠ (m : ℕ) in Filter.atTop, A * (↑m : ℝ) ^ 8 ≤ Real.exp (δ * (↑m : ℝ)))
    : Stmt_Growth configE gE := by
  obtain ⟨K, hK0, hK⟩ := h_Zeta2_Pair_GrowthAux_coeff_le_Iker hPF hV
  obtain ⟨C2, hC20, hC2⟩ := h_Zeta2_Pair_GrowthAux_Iker_le hPF hV (s := 2) le_rfl
  obtain ⟨C4, hC40, hC4⟩ := h_Zeta2_Pair_GrowthAux_Iker_le hPF hV (s := 4) (by norm_num)
  obtain ⟨C5, hC50, hC5⟩ := h_Zeta2_Pair_GrowthAux_Iker_le hPF hV (s := 5) (by norm_num)
  intro ε hε
  have hδ : 0 < 40 * ε := by positivity
  filter_upwards [h_Zeta2_Pair_GrowthAux_eventually_poly_le_exp (K * (C2 + C4 + C5)) hδ, eventually_ge_atTop 1]
    with m hpoly hm
  have hn : ((configE.n m : ℕ) : ℝ) = 40 * m := by rw [h_Zeta2_Pair_configE_n]; push_cast; ring
  have hh : configE.h m = fun p => (m : ℤ) * hE p := rfl
  rw [hn, hh, h_Zeta2_Pair_configE_n]
  set g := Real.exp (-18 / 25 * (40 * m)) with hg
  have hI : ‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖ ≤ (C2 + C4 + C5) * (m : ℝ) ^ 8 * g := by
    have e2 := hC2 m hm
    have e4 := hC4 m hm
    have e5 := hC5 m hm
    rw [← hg] at e2 e4 e5
    linarith
  have hkey : K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖) ≤ Real.exp ((gE + ε) * (40 * m)) := by
    calc K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖)
        ≤ K * ((C2 + C4 + C5) * (m : ℝ) ^ 8 * g) := by gcongr
      _ = (K * (C2 + C4 + C5) * (m : ℝ) ^ 8) * g := by ring
      _ ≤ Real.exp (40 * ε * m) * g := by gcongr
      _ = Real.exp ((gE + ε) * (40 * m)) := by
          rw [hg, ← Real.exp_add, gE]
          congr 1
          ring
  obtain ⟨h1, h2, h3⟩ := hK m hm
  exact ⟨le_trans h1 hkey, le_trans h2 hkey, le_trans h3 hkey⟩
end GrowthAux
end Zeta2.Pair
end
