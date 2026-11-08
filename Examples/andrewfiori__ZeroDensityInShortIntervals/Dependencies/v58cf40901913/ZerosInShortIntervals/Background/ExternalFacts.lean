/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v58cf40901913.ZerosInShortIntervals.Definitions
import Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v58cf40901913.ZerosInShortIntervals.Hypotheses
import Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v58cf40901913.ZerosInShortIntervals.Common.RealLogBounds
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # Facts imported from other sources

`ZerosInShortIntervals.tex` builds on a number of explicit bounds for `ζ` and `Γ`
proved elsewhere; these are recorded here with the originating reference, so that the rest of the
`ZerosInShortIntervals` development can be built on top of them. Each one's doc-comment gives the
`refs.bib` key of its source and, where it was checked against that source directly rather than
transcribed from the paper's citation alone, notes that check and any discrepancy it turned up.

We do *not* prove the external bounds here — the point of this file is to isolate exactly which
external inputs the paper's own arguments rely on. Each is a theorem whose body reads the
corresponding field of a hypothesis class: `Hypotheses.LiteratureInputs` for the twelve
literature bounds, and `BrentStirlingInputs` (declared below, after `logGammaAnalytic`, whose
statements it needs) for Brent's two Stirling expansions. A result depending on one of them says
so in its signature; the project contains no `axiom` and no `sorry`. The provenance discussion
lives here, on each theorem, and the class field carries a one-line pointer back.  That visibility
is what a registry submission requires: the axiom base of any result is readable off its signature.

Two declarations that carry the `[LiteratureInputs]` binder are proved rather than assumed:
`hiary_revers_half_line_bound`, derived from two of the bounds above it, and
`bellotti_wong_Lbound_le`, derived from `bellotti_wong_cor_1_3` together with the power-series
inequality of `Common.RealLogBounds`.

Two blocks are deliberately *outside* that section and so carry no hypothesis binder at all:
`exists_large_nat_cos_ge_half` together with `backlund_trick`, proved outright from Dirichlet's
approximation theorem, and the whole `logGammaAnalytic` development, proved outright from
Mathlib's `Complex.GammaSeq`. The first is load-bearing — it is what keeps
`Littlewood/ArgIntegrals.lean` free of hypothesis binders, which in turn is what makes
`arg_integrals` submittable on its own. See the comment above `exists_large_nat_cos_ge_half`.
-/
set_option linter.unusedSectionVars false
section
variable [LiteratureInputs]
/-- **Hiary–Patel–Yang's half-line bound, Eq. (3.23).** For `|t| > 10¹²`,
`|ζ(1/2+it)| ≤ 0.478013|t|^{1/6}log|t| + 3.853165|t|^{1/6} - 2.914229`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.hiary_eq_3_23`, recording an external result
verbatim. It is the sharper `t`-dependent-constant form of the subconvexity bound on the
critical line.

### Lean Notes
Recorded for completeness as one of the two inputs the source names, but not actually used: the
derivation of `hiary_revers_half_line_bound` below runs on `revers_remark31` instead, which is
sharper in the leading constant (`0.470795` against `0.478013`).

### References
External: Hiary–Patel–Yang, arXiv:2207.02366, `\cite[Eq. (3.23)]{HiaryPatelYang2024}`.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
theorem hiary_eq_3_23 {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.478013 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 3.853165 * |t| ^ (1 / 6 : ℝ) - 2.914229 :=
  LiteratureInputs.hiary_eq_3_23 ht
/-- **Revers' half-line bound, Remark 3.1.** For `|t| ≥ 7·10¹¹`,
`|ζ(1/2+it)| ≤ 0.470795|t|^{1/6}log|t| + 4.04972|t|^{1/6} - 21.5437`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.revers_remark31`, recording an external result
verbatim. It sharpens `hiary_eq_3_23`'s leading constant from `0.478013` to `0.470795`, at the
cost of a larger threshold in the second term.

### Lean Notes
This is the large-`|t|` half of `hiary_revers_half_line_bound`'s two-case derivation.

### References
External: Revers, arXiv:2602.05614, `\cite[Remark 3.1]{Revers2026}`.

### Dependencies
**Depends on:** none.
**Used by:** `hiary_revers_half_line_bound`. -/
theorem revers_remark31 {t : ℝ} (ht : (7 : ℝ) * 10 ^ (11 : ℕ) ≤ |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) - 21.5437 :=
  LiteratureInputs.revers_remark31 ht
/-- **Revers' headline subconvexity bound on the half-line.** For `3 ≤ |t|`,
`|ζ(1/2+it)| ≤ 0.611|t|^{1/6}log|t|`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.revers_subconvexity_bound`, recording an external
result verbatim. It is the improvement of `\cite{Revers2026}` over
`\cite[Theorem 1.1]{HiaryPatelYang2024}`'s `0.618`.

### Lean Notes
Unlike `hiary_revers_half_line_bound` (the sharper *asymptotic* form, better for large `|t|` and
worse for small `|t|`), this holds with a single clean constant across the whole line, which is
what `BackgroundZetaBounds.interpolated_bound_1b` needs as the `σ = 1/2` input to
Phragmén–Lindelöf.

The source's own prose ("recent claimed improvements to …", tex line 1249) flags this as a
*claimed* rather than fully-verified improvement. `BackgroundZetaBounds.interpolated_bound_1a`
anchors its `σ = 1/2` edge on Patel–Yang instead and so avoids the claim altogether; cases (1b)
and (1c) both rest on it — (1b) directly, (1c) through `hiary_revers_half_line_bound` — and the
three are stated side by side so that a consumer can see which `σ = 1/2` bound it inherits.

### References
External: Revers, arXiv:2602.05614, `\cite{Revers2026}`; contrasted
with Hiary–Patel–Yang, `\cite[Theorem 1.1]{HiaryPatelYang2024}`.
tex: quoted in the Appendix, `\S sec:background`.

### Dependencies
**Depends on:** none.
**Used by:** `hiary_revers_half_line_bound`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`. -/
theorem revers_subconvexity_bound {t : ℝ} (ht : 3 ≤ |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.611 * |t| ^ (1 / 6 : ℝ) * Real.log |t| :=
  LiteratureInputs.revers_subconvexity_bound ht
theorem patel_yang_subweyl_bound {t : ℝ} (ht : 3 ≤ t) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 66.7 * t ^ (27 / 164 : ℝ) :=
  LiteratureInputs.patel_yang_subweyl_bound ht
/-- **Yang's explicit bound inside the critical strip.** For every integer `k ≥ 4` and `t ≥ 3`,
with `σ_k := 1 - k/(2^k-2)`, `|ζ(σ_k+it)| ≤ 1.546 t^{1/(2^k-2)} log t`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.yang_critical_strip_bound`, recording an external
result verbatim.

### Lean Notes
This is the source of the constant `log(1.546)` in `JensenScaleConstants.vCoeffPP`, and the
`σ_k` here is the point *near `1`*, matching `sigma`/`interpolated_bound_2`'s own convention. It
matches `ZerosInShortIntervals.tex` exactly (`σ_k := 1-k/(2^k-2)`, `k ≥ 4`), i.e.
`Equation \eqref{eq:sigmak}` (Equation 4).

**Citation check.** Verified against
`Yang-2024-ExplicitBoundsZetaCriticalStripZeroFreeRegion-arXiv.pdf` (Theorem 1.1, requiring
`k ≥ 4`) and against `Fiori-2026-PhragmenLindelofTheorem-JMAA.pdf`'s own "Second example" (§4.2),
which cites exactly this bound at `σ = 5/7 = 1-4/(2^4-2)`.

**Why `k ≥ 4` and not `k ≥ 3`.** The bound is Yang's, and Yang's Theorem 1.1 requires `k ≥ 4`;
`k = 3` would put `σ_k = 1/2`, which that theorem does not cover. The tex agrees: it states the
bound for `k ≥ 4` and special-cases the `σ = 1/2` anchor `vCoeffPP 0` to the sharper half-line
bound of `HIARY2024195`/`revers2026newimprovedexplicitestimate` instead, at the point
`1-k/(2^k-2)` as here.

### References
External: Yang, arXiv:2301.03165, Theorem 1.1, `\cite{Yang2024}`.
tex: `Equation \eqref{eq:sigmak}` (Equation 4) and the `v_k''` display following it.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`, `interpolated_bound_1c`, `interpolated_bound_1c_tight`,
`interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem yang_critical_strip_bound {k : ℕ} (hk : 4 ≤ k) {t : ℝ} (ht : 3 ≤ t) :
    ‖riemannZeta (1 - (k : ℝ) / (2 ^ k - 2) + t * Complex.I)‖
      ≤ 1.546 * t ^ ((1 : ℝ) / (2 ^ k - 2)) * Real.log t :=
  LiteratureInputs.yang_critical_strip_bound hk ht
/-- **Bellotti's Richert-type bound.** For `1/2 ≤ σ ≤ 1` and `|t| ≥ 3`,
`|ζ(σ+it)| ≤ 70.7 |t|^{4.438(1-σ)^{3/2}} (log|t|)^{2/3}`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.bellotti_richert_bound`, recording an external
result verbatim.

### Lean Notes
This is the hypothesis pattern used by `Proposition \ref{prop:Richert}` (Proposition 12) and
`Theorem \ref{thm:circularregions2}` (Theorem 18).

**Citation check.** Verified against the source PDF
(`Bellotti-2023-ZetaBoundsNewZeroFreeRegion-arXiv.pdf`), Abstract. The tex's own statement omits
the lower constraint `1/2 ≤ σ` present in Bellotti's theorem; it is restored here, so the Lean is
if anything more conservative than the source.

### References
External: Bellotti, arXiv:2306.10680, Abstract, `\cite{Bellotti2024}`.
tex: `Proposition \ref{prop:Richert}` (Proposition 12), `Theorem \ref{thm:circularregions2}`
(Theorem 18).

### Dependencies
**Depends on:** none.
**Used by:** `FcrZeta_boundary_le`, `zeta_envelope`. -/
theorem bellotti_richert_bound {σ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 3 ≤ |t|) :
    ‖riemannZeta (σ + t * Complex.I)‖
      ≤ 70.7 * |t| ^ (4.438 * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ) :=
  LiteratureInputs.bellotti_richert_bound hσ ht
/-- **Leong's explicit bound on `-log|ζ(1+it)|`.** For `2 ≤ |t|`,
`-log|ζ(1+it)| ≤ log log|t| + log 29.388`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.leong_log_zeta_one_bound`, recording an external
result verbatim.

### Lean Notes
Stated in the logarithmic form `-log‖ζ(1+it)‖ ≤ log log|t| + log 29.388`, which is the
exponentiated form of Leong's `|1/ζ(1+it)| ≤ 29.388 log t`; this is the shape the downstream
Jensen/Littlewood arguments consume directly. It supplies the `log log|T|` coefficient in
`C_{2,α,r}` of `Theorem \ref{thm:circularregions1}` (Theorem 16).

**Citation check.** Verified against `Leong-2024-ExplicitEstimatesLogDerivativeZeta-arXiv.pdf`:
the paper's Theorem 4 states, for `σ = 1` and `t ≥ 2`, `|1/ζ(1+it)| ≤ 29.388 log t`, matching the
constant `29.388` and hypothesis `2 ≤ |t|` used here exactly.

### References
External: Leong, arXiv:2405.04869, Theorem 4,
`\cite{Leong2024}`.
tex: used in the proof of `Theorem \ref{thm:circularregions1}` (Theorem 16).

### Dependencies
**Depends on:** none.
**Used by:** `circularregions1`, `circularregions1_tight`, `circularregions2`, `littlewoodshort`,
`littlewoodshort_tight`. -/
theorem leong_log_zeta_one_bound {t : ℝ} (ht : 2 ≤ |t|) :
    -Real.log (‖riemannZeta (1 + t * Complex.I)‖) ≤ Real.log (Real.log |t|) + Real.log 29.388 :=
  LiteratureInputs.leong_log_zeta_one_bound ht
end
/- Backlund's trick is proved outright, from Dirichlet's approximation theorem alone, so it is
kept outside the `[LiteratureInputs]` section above.  Everything from here to
`class BrentStirlingInputs` below is unconditional, and a consumer that uses only this block --
`ZerosInShortIntervals.Littlewood.ArgIntegrals` is the one that matters -- inherits no hypothesis
binder.  That is what keeps `arg_integrals` submittable on its own. -/
noncomputable def logGammaTerm (z : ℂ) (n : ℕ) : ℂ :=
  z / ((n : ℂ) + 1) - Complex.log (1 + z / ((n : ℂ) + 1))
noncomputable def logGammaAnalytic (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * z - Complex.log z + ∑' n, logGammaTerm z n
class BrentStirlingInputs where
  /-- Brent's `R₂`, the remainder of the unshifted expansion Eq. (2.1). -/
  remainder : ℂ → ℂ
  /-- Brent's `R̂₂`, the remainder of the shifted expansion Eq. (3.4). -/
  shiftedRemainder : ℂ → ℂ
  /-- Brent, Eq. (2.1): `log Γ(z) = (z-½)log z - z + ½log(2π) + B₂/(2z) + R₂(z)` for `Re z > 0`,
  with `log Γ` read as the analytic branch `logGammaAnalytic`. -/
  expansion : ∀ {z : ℂ}, 0 < z.re →
    logGammaAnalytic z
      = (z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * Real.pi)
        + (bernoulli 2 : ℂ) / (2 * z) + remainder z
  /-- Brent, Corollary 2.2 at `k = 2`: `‖R₂(z)‖ < ‖(1+√(2π))B₄/(12z³)‖` for `Re z > 0`. -/
  remainder_bound : ∀ {z : ℂ}, 0 < z.re →
    ‖remainder z‖ < ‖(1 + Real.sqrt (2 * Real.pi)) * (bernoulli 4 : ℂ) / (12 * z ^ 3)‖
  /-- Brent, Eq. (3.4): the half-shifted expansion
  `log Γ(z+½) = z log z - z + ½log(2π) - 1/(24z) + R̂₂(z)` for `Im z > 5`. -/
  shifted_expansion : ∀ {z : ℂ}, 5 < z.im →
    logGammaAnalytic (z + 1 / 2)
      = z * Complex.log z - z + 1 / 2 * Complex.log (2 * Real.pi) - 1 / (24 * z)
        + shiftedRemainder z
  /-- Brent: `‖R̂₂(z)‖ ≤ (1/100)/‖z‖³` for `Im z > 5` and `|Re z| ≤ 1`. -/
  shifted_remainder_bound : ∀ {z : ℂ}, 5 < z.im → |z.re| ≤ 1 →
    ‖shiftedRemainder z‖ ≤ 1 / 100 / ‖z‖ ^ 3
variable [LiteratureInputs] [BrentStirlingInputs]
theorem fiori_phragmenLindelof {a b : ℝ} (hab : a < b) {r : ℕ} (G : Fin r → ℂ → ℂ)
    (hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b})
    (hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G i s))
    {C1 C2 C3 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3) (hC3b : C3 < Real.pi / (b - a))
    (hG_lower : ∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      C1 * Real.exp (-C2 * Real.exp (C3 * |t|)) < ‖G i (σ + t * Complex.I)‖)
    {f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f {s : ℂ | s.re ∈ Set.Icc a b})
    (hf_upper : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖ < C1 * Real.exp (C2 * Real.exp (C3 * |t|)))
    {α β : Fin r → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hf_a : ∀ t : ℝ, ‖f (a + t * Complex.I)‖ ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i)
    (hf_b : ∀ t : ℝ, ‖f (b + t * Complex.I)‖ ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i)
    {T0 : ℝ}
    (hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)))
    (hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖f (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a))) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖
        ≤ (∏ i, ‖G i (σ + t * Complex.I)‖ ^ α i) ^ ((b - σ) / (b - a))
            * (∏ i, ‖G i (σ + t * Complex.I)‖ ^ β i) ^ ((σ - a) / (b - a)) :=
  LiteratureInputs.fiori_phragmenLindelof hab G hG_holo hG_conj hC1 hC2 hC3 hC3b hG_lower
    hf_holo hf_upper hα hβ hf_a hf_b hG_mono hf_small_t
/-- **Platt–Trudgian's verification of RH to height `3×10¹²`.** Every zero `ρ` of `ζ` with
`0 < Im ρ ≤ 3×10¹²` has `Re ρ = 1/2`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.platt_trudgian_verified_below`, recording the
external computation verbatim.

### Lean Notes
This is `H₀ := 3×10¹²` in the tex's Theorems `\ref{thm:main-jensen}` and
`\ref{thm:main-littlewood}` (Theorems 2 and 3): below `H₀` every zero is known to lie on the
critical line.

`MainTheorem.Nrect_eq_zero_of_le_H0` reads it to conclude `Nrect T₁ T₂ α = 0` whenever `T₂ ≤ H₀`
and `α < 1/2` — a zero counted by `Nrect` has `Re ρ > 1 - α > 1/2`, contradicting `Re ρ = 1/2`.
That is the `t ≤ 10¹²` case of `mainJensen`/`mainLittlewood`. The tex's other use of `H₀` —
shifting the rectangle so its lower edge lands exactly at `H₀` when `T-h < H₀ < T+h` — is vacuous
under those theorems' `h ≤ t^{2/3}`; see `MainTheorem.lean`'s module docstring.

### References
External: Platt–Trudgian, `\cite{PlattTrudgian2021}`.
tex: `Theorem \ref{thm:main-jensen}` (Theorem 2), `Theorem \ref{thm:main-littlewood}`
(Theorem 3).

### Dependencies
**Depends on:** none.
**Used by:** `MainTheorem.Nrect_eq_zero_of_le_H0`. -/
theorem platt_trudgian_verified_below (ρ : ℂ) (him : 0 < ρ.im) (hle : ρ.im ≤ 3 * 10 ^ (12 : ℕ))
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 :=
  LiteratureInputs.platt_trudgian_verified_below ρ him hle hζ
/-- **An explicit zero-density estimate on an interval**, Farzanfard's thesis, Corollary 4.50:
for `T₂ ≥ 3×10¹²` and `σ ∈ [0.75, 1]`,
`N(σ,T₁,T₂) ≤ 12.45321·T₂^{(8/3)(1-σ)}(log T₂)^{5-2σ} + 3.869(log T₂)²`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.farzanfard_zero_density_interval`, recording an
external result verbatim. It is the Ingham/Ramaré zero-density argument in the form given by
Kadiri–Lumley–Ng, refined in the cited thesis and extended there from a half-line count to an
interval count.

### Lean Notes
Stated in this project's `α = 1 - σ` convention, in which `Nrect T₁ T₂ α` counts zeros with
`Re ρ > 1 - α`; so `σ ∈ [0.75,1]` becomes `α ∈ [0, 1/4]`, and the exponents `(8/3)(1-σ)` and
`5-2σ` become `(8/3)α` and `3+2α`.

**Why this source rather than `\cite{KadiriLumleyNg2018}` directly.** The tex cites
Kadiri–Lumley–Ng at this point, but their `N(σ,T)` counts zeros with `0 < Im ρ < T` — a count from
height `0`, not on an interval — and their Theorem 1.1 leaves the constants `C₁, C₂` as functions
of six parameters fixed only in the paper's numerical tables. The thesis's Corollary 4.50 is the
interval form with both constants made numeric, which is what `Nrect` needs.

**The `T₁` hypothesis is the conservative reading.** Corollary 4.50 displays only `T₂ ≥ 3×10¹²`;
its ambient Theorem 4.46 also carries `T₁ > H₀`, with `H₀` the RH-verification height, taken as
`3×10¹²` in the thesis's numerics. The statement here therefore requires `3×10¹² ≤ T₁ ≤ T₂`.
Relaxing the
lower endpoint is not a matter of a sharper citation: for `α < 1/2` every zero counted by `Nrect`
has `Re ρ > 1/2`, so by `platt_trudgian_verified_below` there are none below `3×10¹²` at all, and
`Nrect T₁ T₂ α = Nrect (max T₁ H₀) T₂ α`. `MainTheorem.Nrect_eq_zero_of_le_H0` proves the special
case in which the *whole* window lies below `H₀` (`T₂ ≤ H₀`, giving `Nrect = 0`); the
window-splitting form wanted here, with `T₁ < H₀ < T₂`, is not proved anywhere.

**Coverage: `α ∈ [0,1/4]` only.** Corollary 4.50 is stated for `σ ∈ [0.75,1]`. Both
`MainTheorem.mainJensen` (Theorem 2) and `mainLittlewood` (Theorem 3) assume `α < 1/6`, so every
consumer sits comfortably inside `[0,1/4]`. The range `α ∈ [1/4,1/2)` is intrinsically hard for
an Ingham-type estimate — as `α → 1/2` the count approaches the full zero count in the strip — so
covering it would need a different tool (plausibly the trivial `N(t+h) - N(t-h)` bound), not a
sharper constant here.

**This statement is deliberately the LOSSY form, and a sharper one is available.**
Corollary 4.50 is
doubly weakened relative to its own Theorem 4.46:

* its `U = 12.45321` and `V = 3.869` are the *maxima* over all of `σ ∈ [0.75,1]` (`U` attained at
  the top end, `V` at the bottom). The thesis's Table A.1 gives them per `σ`; in the range this
  project needs, `U` is roughly half — `6.19` at `α = 1/7`, `7.31` at `α = 1/9`.
* it quotes equation (4.160), which is (4.159) weakened by `log(1+y) ≤ y`. The sharper (4.159),
  `N ≤ (T₂-T₁)(log T₂)·log(1 + Y/(T₂-T₁)) + V(log T₂)²` with
  `Y = U·T₂^{(8/3)α}(log T₂)^{2+2α}`, has a leading term *linear in the interval length*
  `T₂-T₁ = 2h` — the same shape as `U_J`'s own `2h` factor — instead of `h`-independent. For the
  short intervals here that is a real gain whenever `Y/(2h)` is not small.

Together those are worth a factor of `3.5` at `α = 1/7`, `2.2` at `α = 1/8`
(`Code/verify_kln_large_h_case.py`, Part 4). That is **not enough** to close the branch — see
`MainTheorem.lean`'s module docstring and `Nrect_le_zero_density_bound` — so the lossy form is
kept here as the simpler statement until something is actually proved from it. Anyone attempting
that branch should start from (4.159) with per-`σ` constants instead.

### References
External: Golnoush Farzanfard, *Explicit zero density for the Riemann zeta function*, MSc thesis,
University of Lethbridge, 2025, Corollary 4.50 (equation (4.180)), specialising her Theorem 4.46;
`\cite{Farzanfard2024}`. Compare Kadiri–Lumley–Ng, *Explicit zero density for the Riemann
zeta function*, J. Math. Anal. Appl. **465** (2018) 22–46, Theorem 1.1 — the half-line antecedent
the tex cites as `\cite{KadiriLumleyNg2018}`.
tex: the `h > t^{2/3}` branch in the proofs of `\ref{thm:main-jensen}` (Theorem 2) and
`\ref{thm:main-littlewood}` (Theorem 3).

**The sharper LOG form, and what it buys.** Corollary 4.50 is
Theorem 4.46 / Remark 4.47 eq. (4.165),
`N(σ,T₁,T₂) ≤ (T₂-T₁)·log T₂·log(1 + U T₂^{(8/3)(1-σ)} (log T₂)^{4-2σ}/(T₂-T₁)) + V log²T₂`
(`T₁ > H₀ = 3·10¹²`, `T₂ > T₀`; `U(σ), V(σ)` from the thesis's Table A.1, maximised over
`σ ∈ [0.75,1]` to `12.45321`, `3.869`), weakened by `log(1+y) ≤ y`. The author suggested the
log form because its shape is `O(h log t)`, like `U_J`/`U_L`.
`Code/indep_mpmath_zero_density_4165.py` quantifies it: the ratio to `U_J`/`U_L` is
decreasing in `h`, so `h = t^{2/3}` stays the binding case, where at `α = 1/6`, `t = 3·10¹²` the
log form improves the ratio from `139` to `17.4` (uniform `U,V`) or `13.5` (per-σ), and lowers
the crossover height from `10^26.1` to `10^23.9` (Jensen) / `10^24.6` (Littlewood) — still far
above `10¹²`; `α ≤ 1/9` closes from `3·10¹²` with per-σ constants. Moving the case boundary to
`h = t^θ` closes the branch for all `t ≥ 3·10¹²` once `θ ≥ 0.82` (`α = 1/6`), `0.76` (`1/7`),
`0.71` (`1/8`). Using (4.165) in Lean would mean a second `LiteratureInputs` field in this shape
(and, for the per-σ constants, the thesis code run at `σ = 5/6, 6/7, …`).

### Dependencies
**Depends on:** `Nrect`.
**Used by:** `MainTheorem.Nrect_le_zero_density_bound`, the `(t-h,t+h)` instance intended for
the `h > t^{2/3}` branch of `MainTheorem.mainJensen` and `mainLittlewood`; see
`Code/verify_kln_large_h_case.py` for why that branch does not close as the tex sketches it. -/
theorem farzanfard_zero_density_interval {α T₁ T₂ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (1 / 4)) (hT₁ : 3 * 10 ^ (12 : ℕ) ≤ T₁) (hT₁₂ : T₁ ≤ T₂) :
    (Nrect T₁ T₂ α : ℝ)
      ≤ 12.45321 * T₂ ^ ((8 : ℝ) / 3 * α) * Real.log T₂ ^ (3 + 2 * α)
        + 3.869 * Real.log T₂ ^ (2 : ℕ) :=
  LiteratureInputs.farzanfard_zero_density_interval hα hT₁ hT₁₂
/-- **Bellotti–Wong, Corollary 1.3 (second estimate): `|N(T) − M(T)| ≤ 0.097 log T + 4.954` for
`T ≥ 1`**, where `M(T) = (T/2π) log(T/(2πe))` (`Common.RealLogBounds.bwM`) is the main term of
the Riemann–von Mangoldt formula.

### Summary of Proof
Not proved here — the field `LiteratureInputs.bellotti_wong_cor_1_3`, recording the cited result
as stated. `N` is the project's counting function `Definitions.N` (zeros with `0 < Im ρ ≤ T`,
with multiplicity), which is the `N(T)` of the paper.

### Lean Notes
The cited result itself is what is assumed; its consequence `bellotti_wong_Lbound_le` (the lower
bound `L(h,t) ≤ N(t+h) − N(t−h)`) is proved below. The step between them is the inequality
`∫₀^λ −log(1−v²) dv ≤ 2(1−log 2)λ³`, `λ = h/t`, i.e. `2λ − φ(λ) ≤ 2(1−log 2)λ³` for
`φ(λ) = (1+λ)log(1+λ) − (1−λ)log(1−λ)`, which `Common.RealLogBounds.two_mul_sub_bwPhi_le`
proves by a power series.

### References
External: Chiara Bellotti and Peng-Jie Wong, *Counting zeros of Artin L-functions*,
`\cite[Cor. 1.3]{BellottiWong2026}` — the second of the two estimates there, valid for `T ≥ 1`.
tex: the display `|N(t) − (t/2π) log(t/2πe)| < 0.097 log|t| + 4.954` above `\ref{cor:main-jensen}`
(Corollary 4), tex line 201 (stated there with `<`; the hypothesis takes the weaker `≤`).

### Dependencies
**Depends on:** `N`, `Common.RealLogBounds.bwM`.
**Used by:** `bellotti_wong_Lbound_le`. -/
theorem bellotti_wong_cor_1_3 {T : ℝ} (hT : 1 ≤ T) :
    |((N T : ℤ) : ℝ) - bwM T| ≤ 0.097 * Real.log T + 4.954 :=
  LiteratureInputs.bellotti_wong_cor_1_3 hT
