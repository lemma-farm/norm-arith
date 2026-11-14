import Mathlib

-- ==== Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v7526a7958bd3.ZerosInShortIntervals.Common.RealLogBounds ====
section
/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # Small reusable numeric `Real.log` bounds

Three small numeric facts (`2 < log x` for `8 < x`, `1 < log x` for `3 ≤ x`, and `4 ≤ log x` for
`55 ≤ x`), each needed at several call sites that would otherwise re-derive `Real.exp 2 < 8`,
`Real.exp 1 < 3` or `Real.exp 4 < 55` from `Real.exp_one_lt_d9` inline. They are collected here so
that the derivation happens once; each theorem's `Used by` lists its call sites.

Also here: the elementary analysis behind Bellotti–Wong's lower bound `L(h,t)` on
`N(t+h) − N(t−h)` — the power series of `φ(x) = (1+x)log(1+x) − (1−x)log(1−x)`
(`hasSum_two_mul_sub_bwPhi`), the sharp inequality `2x − φ(x) ≤ 2(1−log 2)x³` on `[0,1)`
(`two_mul_sub_bwPhi_le`), the resulting bound on `M(t+h) − M(t−h)` for the Riemann–von Mangoldt
main term `M` (`bwM_sub_ge`), and the assembly `bw_Lbound_of_cor` that
`ExternalFacts.bellotti_wong_Lbound_le` applies to the cited Corollary 1.3.

Two integral facts about `log(1 − v²)` sit here too: the crude estimate
`integral_neg_log_one_sub_sq_le` and the exact antiderivative
`hasDerivAt_log_one_sub_sq_antideriv` / `integral_log_one_sub_sq`. They belong to the same
`L(h,t)` circle of ideas but are not on the route the assembly above takes, which needs no
integral at all; see their own docstrings. -/
/-- **`M(T) := (T/2π) log(T/(2πe))`**, the main term of the Riemann–von Mangoldt formula.

### Summary of Proof
A definition.

### References
The `N(t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex line 201;
Bellotti–Wong, `\cite[Cor. 1.3]{BellottiWong2026}`.

### Dependencies
**Depends on:** none.
**Used by:** `bwM_sub_ge`, `bw_Lbound_of_cor`, `Hypotheses.LiteratureInputs.bellotti_wong_cor_1_3`
and the theorem `ExternalFacts.bellotti_wong_cor_1_3` that reads it,
`ExternalFacts.bellotti_wong_Lbound_le`. -/
noncomputable def bwM (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

end

-- ==== Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v7526a7958bd3.ZerosInShortIntervals.Definitions ====
section
/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # Core definitions for "Zero Density Theorems for Short Intervals"

This file collects the basic definitions from `ZerosInShortIntervals.tex`
(A. Fiori, *Zero Density Theorems for Short Intervals*) that are used throughout the
`ZerosInShortIntervals` development. No hypothesis-class section variable is declared here, so every
statement in this file is unconditional.

We count zeros of `riemannZeta` with multiplicity using the divisor `MeromorphicOn.divisor` from
`Mathlib.Analysis.Meromorphic.Divisor` (the same object that drives Mathlib's Jensen's formula,
`Mathlib.Analysis.Complex.JensenFormula`). For a set `U` on which `riemannZeta` is (automatically)
meromorphic, `∑ᶠ u, MeromorphicOn.divisor riemannZeta U u` is the number of zeros of `ζ` in `U`
counted with multiplicity, offset by the order of any pole of `ζ` lying in `U`. The only pole is
`s = 1`, whose imaginary part is `0`, so every region below that carries a positive lower bound on
`Im s` is pole-free and the sum is a genuine zero count (`Nrect_nonneg`, `NlineRe_nonneg`).
`Ncirc`, by contrast, is defined for an arbitrary closed ball and so carries no such guarantee by
construction.

### Zero-counting functions
- `N T`: the number of zeros `ρ` of `ζ` with `0 < Im ρ ≤ T`.
- `Ncirc s α`: the number of zeros `ρ` of `ζ` with `|ρ - s| ≤ α`, i.e. `N(s,α)` in the source.
- `Nrect T₁ T₂ α`: the number of zeros `ρ` of `ζ` with `T₁ < Im ρ ≤ T₂` and `Re ρ > 1 - α` — the
  half-open window, top edge included and bottom edge excluded, in which the whole development
  and the registry submission are stated.
- `NlineRe T α`: the zeros on the single horizontal line `Im ρ = T` with `Re ρ > 1 - α`.
- `Nhalf T₁ T₂ α`: the source's own `N(T₁,T₂,α)`, which counts a zero on either horizontal edge
  of the closed window `T₁ ≤ Im ρ ≤ T₂` with half its multiplicity.
- `zetaOrd u`: the order of vanishing of `ζ` at `u`, the pointwise summand behind all of these.

### Other recurring quantities
- `Phi`: the function `Φ(s) = ∑_{n>1} Λ(n)/(log n)² n^{-s}` of Equation `\ref{eq:phis}`
  (Equation 12), an antiderivative of `-log ζ(s)`.
- `hatAlpha`: `α̂_r = √(r² - α²)` from Equation `\ref{eq:hatalpha}` (Equation 10).
- `eta`: the constant `η ∈ (0,1)` solving `1 + η + log η = 0` from Equation `\ref{eq:eta}`
  (Equation 15).
- `stieltjesConstant1`: the first Stieltjes constant `γ₁`, together with the convergence proof and
  the explicit two-sided bracketing that make numerical claims about it provable.
-/
open scoped ArithmeticFunction
/-- **`N T` is the number of zeros `ρ` of `ζ` (with multiplicity) satisfying `0 < Im ρ ≤ T`.**

### Summary of Proof
A definition: the sum of the divisor of `ζ` over the half-strip `{0 < Im s ≤ T}`. This is `N(T)`
in the introduction of the source.

### References
tex: the definition of `N(T)` in the introduction (page 1).

### Dependencies
**Depends on:** none.
**Used by:** `Hypotheses.LiteratureInputs.bellotti_wong_cor_1_3`,
`ExternalFacts.bellotti_wong_cor_1_3`, `MainCorollary.Lbound_le_N_sub_N`, and
`HalvingConvention.N_sub_N_eq_Nrect_one`. -/
noncomputable def N (T : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.im ∧ s.im ≤ T} u
/-- **`Nrect T₁ T₂ α` is the number of zeros `ρ` of `ζ` (with multiplicity) satisfying
`T₁ < Im ρ ≤ T₂` and `Re ρ > 1 - α`.**

### Summary of Proof
A definition: the sum of the divisor of `ζ` over the half-open window `{T₁ < Im s ≤ T₂}` cut by
the open half-plane `{Re s > 1 - α}`. The window is half-open on purpose — the top edge counts in
full, the bottom edge not at all — which makes `Nrect` additive in the height range
(`Nrect_add_split`). This is the unhalved variant of the source's `N(T₁,T₂,α)`; the source's own
half-multiplicity convention for edge zeros is `Nhalf`, and the two agree whenever both edges are
zero-free (`Nhalf_eq_Nrect_of_forall_ne_zero`). Every statement of the development and of the
registry submission is phrased with `Nrect`.

### References
tex: the definition of `N(T₁,T₂,α)` in the introduction (page 1).

### Dependencies
**Depends on:** none.
**Used by:** `Nrect_mono`, `Nrect_nonneg`, `Nhalf`, `Nrect_add_split`, `two_mul_Nhalf_eq`,
`Nsigma`, `jensenrectangle`, `littlewoodshort`,
`littlewoodshort_tight`, `mainJensen`, `mainJensenTight`, `mainLittlewood`, `mainLittlewoodTight`,
`mainPositiveProportionCorollary_jensen`, `mainPositiveProportionCorollary_littlewood`,
`rectangularjensen`, `rectangularjensen_tight`, `simplelittlewoodzerodensity`. -/
noncomputable def Nrect (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} u

end

-- ==== Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v7526a7958bd3.ZerosInShortIntervals.Hypotheses ====
section
/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # The project's unproved inputs, as hypotheses

Everything this development assumes rather than proves is collected here and in three companion
classes declared further down the import graph (`ExternalFacts.BrentStirlingInputs`,
`LogDerivZetaLaurent.LaurentCertificate`, `BackgroundZetaBounds.InterpolationCertificates`), each
placed at the first point where its statements can be written.  A result that needs one of them
says so in its signature; nothing is assumed silently.

**Two kinds, deliberately kept apart.**

* `LiteratureInputs` — results taken from other people's papers.  These are ordinary mathematics,
  published and refereed; the project's claim is only that it has transcribed them correctly, and
  each field's docstring names the source.  The full provenance discussion (edition, page, which
  numbered statement, and any discrepancy found while checking) stays on the corresponding
  theorem in `Background/ExternalFacts.lean`, which is where a reader should look.
* `NumericCertificates` — finite numerical facts that are true, that the project has certified
  outside Lean by ball arithmetic (Sage/arb) or independent high-precision evaluation (mpmath),
  and that today's Mathlib cannot express as a proof term: there is no verified evaluation of `ζ`,
  and no sharp enclosure of `Γ(1/4)`.  The certifying script is named in each field's docstring
  and lives in `Code/`.

The two are on very different footings and a reader is entitled to weigh them differently, which
is why they are not one class.

**Why classes and not axioms.**  An `axiom` is invisible at the use site and makes
`#print axioms` the only way to discover it.  A class field appears in the signature of every
result that depends on it, and a proved `Solution` module that instantiates nothing depends on no
axiom at all — which is what the Palomar Registry requires of a submission.  Conditional results
state their hypotheses.

**The bundle.** `ZerosInShortIntervals.AllHypotheses.ZeroDensityHypotheses` gathers all five classes
into one, for the headline statements. -/
/-- **The results this project takes from the literature.**

Each field is a published theorem, transcribed.  The full citation, the edition checked, and any
discrepancy found during checking are recorded on the corresponding theorem in
`Background/ExternalFacts.lean` (and, for `riemannZeta_lowest_zero_height`, in
`Background/LogDerivZetaLaurent.lean`); the one-line pointers below say only which paper each
field comes from.

### Summary of Proof
A class; no proof.  It has no instance in this repository, by design: every theorem that needs one
of these results carries `[LiteratureInputs]`, so the dependency is visible in its type.

### Lean Notes
`Prop`-valued, so instances are proof-irrelevant and two of them cannot disagree.

### References
tex: the paper's own citations; `refs.bib` at the repository root carries each one's DOI or arXiv
identifier.

### Dependencies
**Depends on:** `Definitions.N`, `Definitions.Nrect`, `Common.RealLogBounds.bwM`.
**Used by:** the twelve `Background.ExternalFacts` theorems that read its fields, and transitively
the headline theorems.  `LogDerivZetaLaurent.riemannZeta_lowest_zero_height` reads the last
field. -/
class LiteratureInputs : Prop where
  /-- Hiary–Patel–Yang, Eq. (3.23): the explicit sixth-power bound on the critical line for
  `|t| > 10^12`.  See `ExternalFacts.hiary_eq_3_23`. -/
  hiary_eq_3_23: ∀ {t : ℝ}, (10 : ℝ) ^ (12 : ℕ) < |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.478013 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 3.853165 * |t| ^ (1 / 6 : ℝ) - 2.914229
  /-- Revers, Remark 3.1: the same shape with sharper constants, from `7·10^11`.
  See `ExternalFacts.revers_remark31`. -/
  revers_remark31 : ∀ {t : ℝ}, (7 : ℝ) * 10 ^ (11 : ℕ) ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) - 21.5437
  /-- Revers: the clean subconvexity bound `0.611 |t|^{1/6} log|t|` valid from `|t| ≥ 3`.
  See `ExternalFacts.revers_subconvexity_bound`. -/
  revers_subconvexity_bound : ∀ {t : ℝ}, 3 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.611 * |t| ^ (1 / 6 : ℝ) * Real.log |t|
  /-- Patel–Yang: the sub-Weyl bound `66.7 t^{27/164}` on the critical line.
  See `ExternalFacts.patel_yang_subweyl_bound`. -/
  patel_yang_subweyl_bound : ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 66.7 * t ^ (27 / 164 : ℝ)
  /-- Yang, *Explicit bounds on ζ in the critical strip*, Theorem 1.1, for `k ≥ 4`.
  See `ExternalFacts.yang_critical_strip_bound`. -/
  yang_critical_strip_bound : ∀ {k : ℕ}, 4 ≤ k → ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 - (k : ℝ) / (2 ^ k - 2) + t * Complex.I)‖
      ≤ 1.546 * t ^ ((1 : ℝ) / (2 ^ k - 2)) * Real.log t
  /-- Bellotti's explicit form of Richert's bound inside the critical strip.
  See `ExternalFacts.bellotti_richert_bound`. -/
  bellotti_richert_bound : ∀ {σ t : ℝ}, σ ∈ Set.Icc (1 / 2 : ℝ) 1 → 3 ≤ |t| →
    ‖riemannZeta (σ + t * Complex.I)‖
      ≤ 70.7 * |t| ^ (4.438 * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ)
  /-- Leong, *Explicit estimates for the logarithmic derivative of ζ*, Theorem 4: a lower bound
  for `|ζ(1+it)|`.  See `ExternalFacts.leong_log_zeta_one_bound`. -/
  leong_log_zeta_one_bound : ∀ {t : ℝ}, 2 ≤ |t| →
    -Real.log (‖riemannZeta (1 + t * Complex.I)‖) ≤ Real.log (Real.log |t|) + Real.log 29.388
  /-- Fiori, *A note on the Phragmén–Lindelöf theorem*, J. Math. Anal. Appl. **559** (2026) no. 1,
  130404, doi:10.1016/j.jmaa.2026.130404,
  Theorem 7 — the interpolation principle the appendix's `ζ` bounds are built on.  **This is the
  cited paper's Theorem 7, not this project's Proposition 8.**
  See `ExternalFacts.fiori_phragmenLindelof`. -/
  fiori_phragmenLindelof : ∀ {a b : ℝ}, a < b → ∀ {r : ℕ} (G : Fin r → ℂ → ℂ),
    (∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b}) →
    (∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G i s)) →
    ∀ {C1 C2 C3 : ℝ}, 0 < C1 → 0 < C2 → 0 < C3 → C3 < Real.pi / (b - a) →
    (∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      C1 * Real.exp (-C2 * Real.exp (C3 * |t|)) < ‖G i (σ + t * Complex.I)‖) →
    ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f {s : ℂ | s.re ∈ Set.Icc a b} →
    (∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖ < C1 * Real.exp (C2 * Real.exp (C3 * |t|))) →
    ∀ {α β : Fin r → ℝ}, (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) →
    (∀ t : ℝ, ‖f (a + t * Complex.I)‖ ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i) →
    (∀ t : ℝ, ‖f (b + t * Complex.I)‖ ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i) →
    ∀ {T0 : ℝ},
    (∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b))) →
    (∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖f (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a))) →
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖
        ≤ (∏ i, ‖G i (σ + t * Complex.I)‖ ^ α i) ^ ((b - σ) / (b - a))
            * (∏ i, ‖G i (σ + t * Complex.I)‖ ^ β i) ^ ((σ - a) / (b - a))
  /-- Platt–Trudgian: the Riemann hypothesis is verified up to height `H₀ = 3·10^12`.
  See `ExternalFacts.platt_trudgian_verified_below`. -/
  platt_trudgian_verified_below : ∀ (ρ : ℂ), 0 < ρ.im → ρ.im ≤ 3 * 10 ^ (12 : ℕ) →
    riemannZeta ρ = 0 → ρ.re = 1 / 2
  /-- Farzanfard, *Explicit zero density for ζ* (MSc thesis, U. of Lethbridge): the classical
  zero-density bound on an interval, used only for the `h ≫ t^{2/3}` regime.
  See `ExternalFacts.farzanfard_zero_density_interval`. -/
  farzanfard_zero_density_interval : ∀ {α T₁ T₂ : ℝ},
    α ∈ Set.Icc (0 : ℝ) (1 / 4) → 3 * 10 ^ (12 : ℕ) ≤ T₁ → T₁ ≤ T₂ →
    (Nrect T₁ T₂ α : ℝ)
      ≤ 12.45321 * T₂ ^ ((8 : ℝ) / 3 * α) * Real.log T₂ ^ (3 + 2 * α)
        + 3.869 * Real.log T₂ ^ (2 : ℕ)
  /-- Bellotti–Wong, Corollary 1.3: `|N(T) - M(T)| ≤ 0.097 log T + 4.954` for `T ≥ 1`, the lower
  bound for the denominator of every proportion statement.
  See `ExternalFacts.bellotti_wong_cor_1_3`. -/
  bellotti_wong_cor_1_3 : ∀ {T : ℝ}, 1 ≤ T →
    |((N T : ℤ) : ℝ) - bwM T| ≤ 0.097 * Real.log T + 4.954
  /-- The lowest nontrivial zero of `ζ` has ordinate above `14` (classical; it is `14.1347…`).
  See `LogDerivZetaLaurent.riemannZeta_lowest_zero_height`. -/
  riemannZeta_lowest_zero_height : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    14 < |ρ.im|

end

-- ==== Examples.andrewfiori__ZeroDensityInShortIntervals.Dependencies.v7526a7958bd3.ZerosInShortIntervals.Background.ExternalFacts ====
section
/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
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

end
/- Backlund's trick is proved outright, from Dirichlet's approximation theorem alone, so it is
kept outside the `[LiteratureInputs]` section above.  Everything from here to
`class BrentStirlingInputs` below is unconditional, and a consumer that uses only this block --
`ZerosInShortIntervals.Littlewood.ArgIntegrals` is the one that matters -- inherits no hypothesis
binder.  That is what keeps `arg_integrals` submittable on its own. -/
/-- **The `n`-th Weierstrass term of `log Γ`:** `z/(n+1) - log(1 + z/(n+1))`, principal logarithm.

### Summary of Proof
Definition.  For `z` in the slit plane so is `1 + z/(n+1)` (`one_add_div_mem_slitPlane`), so the
term is analytic there; it is `O(‖z‖²/n²)` (`norm_logGammaTerm_le`).

### References
Whittaker–Watson §12.1, the Weierstrass product `1/Γ(z) = z e^{γz} ∏ (1 + z/n) e^{-z/n}`.

### Dependencies
**Depends on:** none.
**Used by:** `norm_logGammaTerm_le`, `summable_logGammaTerm`, `differentiableOn_logGammaTerm`,
`logGammaAnalytic`, `logGammaPartial`, `exp_logGammaPartial`,
`differentiableOn_logGammaAnalytic`, `logGammaAnalytic_ofReal_im`. -/
noncomputable def logGammaTerm (z : ℂ) (n : ℕ) : ℂ :=
  z / ((n : ℂ) + 1) - Complex.log (1 + z / ((n : ℂ) + 1))
/-- **The analytic branch of `log Γ` on the slit plane — Brent's `ln Γ` — as the Weierstrass
series** `logGammaAnalytic z = -γz - log z + Σ_{n≥1} (z/n - log(1 + z/n))`, principal logarithms.

### Summary of Proof
Definition.  `exp_logGammaAnalytic` shows `exp ∘ logGammaAnalytic = Γ` on the slit plane
`ℂ \ (-∞, 0]`, `differentiableOn_logGammaAnalytic` that it is holomorphic there, and
`logGammaAnalytic_ofReal_im` that it is real on the positive real axis — which together
characterise Brent's `ln Γ` (the holomorphic logarithm of `Γ` on the cut plane that is real for
positive real arguments), so the Stirling expansions below are statements about *this* function.

### Lean Notes
Mathlib has only the principal branch `Complex.log ∘ Complex.Gamma`, which jumps by `2π` in its
imaginary part and cannot satisfy the Stirling expansions (see the section header); the series
definition avoids the branch problem entirely.  Off the slit plane the series still converges,
but nothing is claimed about it there.

### References
Whittaker–Watson §12.1; Brent, `\cite{Brent2019}`, §2 (the paragraph defining `ln Γ`).

### Dependencies
**Depends on:** `logGammaTerm`.
**Used by:** `BrentStirlingInputs` (all four of its `Prop` fields), `exp_logGammaAnalytic`,
`differentiableOn_logGammaAnalytic`, `logGammaAnalytic_ofReal_im`, `brent_stirling_expansion`,
`brent_stirling_shifted_expansion`, `BackgroundZetaBounds.re_logGammaAnalytic_eq`,
`BackgroundZetaBounds.log_norm_Gamma_eq_re_logGammaAnalytic`,
`BackgroundZetaBounds.logGammaAnalytic_shift_im`,
`BackgroundZetaBounds.arg_Gamma_eq_logGammaAnalytic_im_add_int`,
`BackgroundZetaBounds.argGamma_analytic`, `BackgroundZetaBounds.argGamma`. -/
noncomputable def logGammaAnalytic (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * z - Complex.log z + ∑' n, logGammaTerm z n
/-- **Brent's explicit Stirling expansions for `log Γ`, as a hypothesis class.**

R. P. Brent, *Asymptotic approximation of central binomial coefficients with rigorous error
bounds*, `\cite{Brent2019}`: Eq. (2.1) with Corollary 2.2's remainder bound at `k = 2`, and the
shifted Eq. (3.4).  Both expansions name a remainder function and then bound it, so the class
carries the two functions as **data** and the four statements about them as `Prop` fields; that is
the honest reading of "there is a remainder with these properties".  It is the reason this class,
unlike `Hypotheses.LiteratureInputs` and `Hypotheses.NumericCertificates`, is not `Prop`-valued.

It is declared here rather than in `Hypotheses.lean` because its statements mention
`logGammaAnalytic`, which is defined above in this file.

The full provenance — which edition was checked, the principal-branch encoding that would make
this material *inconsistent*, and why the analytic branch `logGammaAnalytic` rather than
`Complex.log ∘ Complex.Gamma` is the right object — is on the six declarations below, which read
their content off this class.

### Summary of Proof
A class; no proof.

### Lean Notes
`brent_stirling_remainder` and `brentShiftedRemainder` are thin `def`s over the two data fields,
so the four expansions below can be stated in Brent's own notation for `R₂` and `R̂₂`.

### References
External: Brent, `\cite{Brent2019}`, Eq. (2.1), Corollary 2.2, Eq. (3.4).

### Dependencies
**Depends on:** `logGammaAnalytic`.
**Used by:** `brent_stirling_remainder`, `brentShiftedRemainder`, `brent_stirling_expansion`,
`brent_stirling_remainder_bound`, `brent_stirling_shifted_expansion`,
`brent_stirling_shifted_remainder_bound`. -/
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

end

-- ==== Examples.andrewfiori__ZeroDensityInShortIntervals.Examples.Example_491a47c9a7a35c528526_PhragmenLindelofSetup ====
/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # Shared Phragmén–Lindelöf building blocks (`\S sec:background`)

This file collects the reusable pieces needed to instantiate `fiori_phragmenLindelof`
(Fiori's Theorem 7, doi:10.1016/j.jmaa.2026.130404, available here as
`ExternalFacts.fiori_phragmenLindelof`, a theorem reading the `LiteratureInputs` field of the same
name) for the four `interpolated_bound_*` propositions in `BackgroundZetaBounds.lean`.

**Why the decomposition has the shape it does.** The paper's own worked "Third example" (§4.3) is
the direct source for `interpolated_bound_1a`, but its displayed formula
`|ζ(σ+it)| ≤ (66.7|σ+it|^{27/164})^{w_a}·(1.546|σ+it|^{1/14}|G(σ+it)|)^{w_b}` (with
`G(s)=(1/2)(log(4e+s)+log(4e+2-s))`, `w_a=(b-σ)/(b-a)`, `w_b=(σ-a)/(b-a)`) is *not* literally an
instance of `fiori_phragmenLindelof`'s conclusion for a single `r=1` function `G`: matching the
exact displayed constants forces an **`r=3`** decomposition, which reproduces
`interpolated_bound_1a`'s stated coefficients `47/123-107/246σ` and `14/3(σ-1/2)` exactly (the
resulting linear system is solved and checked in `sympy`):
* `G₁(s) = 66.7^(164/27) · s`, exponents `(α₁,β₁) = (27/164, 0)` — carries *both* the sub-Weyl
  power growth and the `66.7` constant, contributing only at the `σ=1/2` boundary (its `β₁=0`
  kills it at `σ=5/7`). Needs `|G₁|` increasing in `σ` (holds: `α₁>β₁`, `|C·s|` increasing on
  `Re s>0`).
* `G₂(s) = 1.546^14 · (Q'-s)` for any fixed `Q' > 5/7` (e.g. `Q'=1`), exponents
  `(α₂,β₂) = (0, 1/14)` — the mirror image, carrying the Yang power growth and the `1.546`
  constant, contributing only at `σ=5/7`. Needs `|G₂|` decreasing in `σ` (holds: `β₂>α₂`, `|Q'-s|`
  decreasing on `Re s<Q'`).
* `G₃ = GPL 4e`, exponents `(α₃,β₃) = (0,1)` — the log-type function, contributing only at
  `σ=5/7` (matching `log|G(σ+it)|`, i.e. `loglog|t|`, in the target).

A single `G₀ = s` with *both* `(α₀,β₀) = (27/164,1/14)` nonzero (no split) is algebraically
equivalent and reproduces the same `log|t|` coefficient; the split exists *only* to also match the
two separate boundary constants `66.7`,`1.546`, which a single scaled `s` cannot do simultaneously
at both ends, since a single scalar multiple contaminates both exponents.

`interpolated_bound_1b` reuses `G₂,G₃` verbatim but replaces `G₁` (new constant, exponent `1/6`)
and switches `G₃`'s exponents to `(α₃,β₃)=(1,1)` (**equal**, Corollary 3 / Remark 4's device for a
`G` that is not monotone in `σ`, here used deliberately: `|GPL|` is *not* known to be monotone
with the exponent pattern `1b` needs, but equal exponents make `hG_mono` hold vacuously — see
`fiori_phragmenLindelof`'s `hG_mono`, whose two implications are vacuous when `α i = β i`) — which
is also why `1b`'s `loglog|T|` coefficient is the constant `1` (`= w_a+w_b`) rather than `1a`'s
`σ`-dependent `14/3(σ-1/2)` (`= w_b·1`, since `1a` uses `α₃=0`). `interpolated_bound_1c` keeps
`G₂,G₃` as well, but its `σ=1/2` boundary bound is affine in `log|t|`, so its `G₁` is the affine
`G1shift` rather than a scaled `s`, and `G₃` keeps `(α₃,β₃)=(0,1)` with the monotonicity supplied
outright by `GPL_anti_of_large_t`; its `loglog|T|` coefficient is again the flat `1`, this time
because `G₁`'s own `log` contributes `w_a` and `G₃`'s contributes `w_b`. That case has its own
`r=4` family — see the `### Case (1c)` section below.

`interpolated_bound_2` (general `k≥4`, interpolating Yang's bound at consecutive `k,k+1`) uses the
exact same *shape*: `G₁` carries `1.546^(2^k-2)·s` with exponent `1/(2^k-2)` (only at `σ=a_k`),
`G₂` carries `1.546^(2^{k+1}-2)·(Q'-s)` with exponent `1/(2^{k+1}-2)` (only at `σ=b_k`), and
`G₃ = GPL e` with equal exponents `(1,1)`. Solving for the exponents that make the interpolation
match the stated `(1-σ)/(k-1+2^{1-k}) - 1/(2^k(k-1)+2)` coefficient exactly (matching value at
`σ=a_k` and `σ=b_k`) confirms — via `sympy`, checked at `k=4,5,6,7` — that the needed exponents
are `1/(2^k-2)` and `1/(2^{k+1}-2)`, i.e. **exactly** `ExternalFacts.yang_critical_strip_bound`'s
own *exponent* at `k` and at `k+1` respectively — not the `k/(2^k-2)` that appears in the same
statement as the abscissa `σ_k = 1 - k/(2^k-2)`.

**Proved outright here** (so that every `interpolated_bound_*` proof gets them for free):
holomorphy and conjugate symmetry of all three `G` shapes; strict monotonicity in `σ` of the two
*linear* shapes; uniform positive lower bounds for all three on the strip
(`linG_lower_const`/`linGRefl_lower_const`/`GPL_lower_const`); the reduction
`envelope_of_const_lower`, which turns "each `‖Gᵢ‖ ≥` a positive constant" plus "`f` has *some*
two-exponential envelope" into the *shared* `(C1,C2,C3)` envelope `fiori_phragmenLindelof`
demands, and its packaged form `exists_shared_envelope`; the window lemmas
`abs_log_sub_log_le'`/`abs_log_sub_log_le` and `twenty_lt_log`; the reflection
`zeta_norm_abs_im`; the Yang-interval arithmetic (`add_two_lt_two_pow`, `two_lt_two_pow`,
`half_le_sigmaYang`, `sigmaYang_mem_Ioo`, `sigmaYang_lt_succ`) and the coefficient identity
`yang_interp_coeff_eq`; and — the workhorses downstream — the `log`-form bridges
`log_bound_of_interp`, `log_bound_of_interp_1c` and `log_bound_of_interp_self`, which take the
multiplicative conclusion of `fiori_zeta_interpolation`/`fiori_zeta_interpolation_1c` to the
additive, `3/T`-slack form the four `interpolated_bound_*` propositions are stated in.

**This file contains no `sorry` and no `axiom`.** Both facts the source verifies only numerically
are proved outright — the `|t|>T0` monotonicity in `σ` of `‖GPL Q‖` (`GPL_anti_of_large_t`, which
also *corrects* the threshold from `|t|>3` to `|t|>Q+1` and restricts the range to `σ ≤ 1`) and
its `≥ log|t|` lower bound (`GPL_ge_log`, which needs no hypotheses on `σ` or `Q` at all). The
double-exponential envelope for `(s-1)ζ(s)` on each strip (`zeta_envelope`), the remaining input
to the growth hypothesis of `fiori_phragmenLindelof`, is proved too. Downstream, the compact-range
(`|t| ≤ T0`) numeric check each `interpolated_bound_*` needs is a hypothesis rather than a proof:
a field of `BackgroundZetaBounds.InterpolationCertificates` (cases 1a, 1b, 1c) or of
`BackgroundZetaBounds.Hcompact2Certificates` (case 2), each certified outside Lean by ball
arithmetic in `Code/`.

**Why `hG_conj` is scoped to the strip.** `fiori_phragmenLindelof` asks for
`Gᵢ(s̄) = conj(Gᵢ(s))` only for `s.re ∈ Set.Icc a b`, and that restriction is essential for the
log-type `G` the source's own §4 examples use: for `GPL Q` the unrestricted `∀ s : ℂ` form is
false at real `s ≤ -Q`, where `Q+s` sits on `Complex.log`'s branch cut
(`Complex.log(Q+s) = log|Q+s| + iπ`, so a `+iπ/2` term appears which cannot be
conjugation-symmetric at a point where `conj s = s`). The source scopes the condition the same way
(Theorem 1: "… holomorphic for `Re(s) ∈ [a,b]`, have `Gᵢ(s̄) = conj(Gᵢ(s))`"), and its proof of
Lemma 5 only ever evaluates `Gᵢ` inside the strip. The restriction is symmetric in `s` and
`conj s`, since `(conj s).re = s.re`, and `GPL_conj` below discharges it outright. -/
noncomputable section
open Complex
/- The half-line and critical-strip bounds this file instantiates are hypotheses, collected in the
classes `LiteratureInputs` (`ZerosInShortIntervals/Hypotheses.lean`) and `BrentStirlingInputs`
(`Background/ExternalFacts.lean`); nothing here is an `axiom`.

Lean automatically includes an instance-implicit section variable in every *theorem* in scope,
whether or not that theorem's proof reaches it (definitions are not affected).  So the
binders below appear on more statements than strictly need them; each such statement is still
true, merely stated under a hypothesis it does not use.  Precision is recovered where it matters,
on the headline results: see `ZerosInShortIntervals/AllHypotheses.lean`.  The linter that reports
the unused ones is silenced here rather than answered with hundreds of `omit` clauses. -/
set_option linter.unusedSectionVars false
variable [LiteratureInputs] [BrentStirlingInputs]

/-- `GPL Q s = (1/2)(log(Q+s) + log(Q+2-s))`: the log-type function used in Fiori's "Second" (`Q=e`)
and "Third" (`Q=4e`) worked examples.

### Summary of Proof
A definition, not a theorem. `GPL Q` is the log-type auxiliary function of Fiori's worked examples,
symmetric about `σ = 1`: the two logarithms `log(Q+s)` and `log(Q+2-s)` swap when `s ↦ 2-s`. That
symmetry is what makes `‖GPL‖` monotone in `σ` away from the centre, which is the hypothesis
Phragmén–Lindelöf needs. The source uses `Q = e` in its "Second example" and `Q = 4e` in its
"Third"; this project instantiates at `Q = 4e` (cases 1a and 1c), `Q = 16` (case 1b, chosen large
enough that `GPL 16` clears that case's compact-range check) and `Q = e` (case 2).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `G1shift`, `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`, `GPL_anti_of_large_t`,
`GPL_conj`, `GPL_ge_log`, `GPL_holomorphicOn`, `GPL_im_eq`, `GPL_le_log`, `GPL_le_log_tight`,
`GPL_lower_const`, `GPL_mono_of_large_t`, `GPL_reSq_lt_of_large_t`, `GPL_re_eq`,
`GPL_re_mono_of_large_t`, `exists_shared_envelope`, `fiori_zeta_interpolation`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`,
`fiori_zeta_interpolation_tight`, `interpG`, `interpG1c`, `interpG_prod_α`, `interpG_prod_β`. -/
def GPL (Q : ℝ) : ℂ → ℂ :=
  fun s => (1 / 2) * (Complex.log ((Q : ℂ) + s) + Complex.log ((Q : ℂ) + 2 - s))

/-! ### `Re`, `Im` and monotonicity of `GPL`

Both facts the source verifies numerically — that `‖GPL Q(σ+it)‖` decreases in `σ` for large `|t|`,
and that it is at least `log|t|` — are proved here in closed form. Writing `A = Q+σ`, `B = Q+2-σ`
(so `A+B = 2Q+2` is independent of `σ`, `AB = (Q+1)² - (1-σ)²`, and `B-A = 2(1-σ)`):

  `Re GPL Q(σ+it) = ¼(log(A²+t²) + log(B²+t²))`,
  `Im GPL Q(σ+it) = ½(arctan(t/A) - arctan(t/B))`.

`GPL_ge_log` is then immediate from `‖z‖ ≥ Re z` and `A²+t², B²+t² ≥ t²`. For
`GPL_anti_of_large_t`, both `Re` and `|Im|` are shown to decrease in `σ` on `σ ≤ 1`. -/

/-- `G1shift Q c d s := c·GPL Q (s+1) + d`.

### Summary of Proof
A definition, not a theorem. `G1shift Q c d s = c·GPL Q(s+1) + d` is the shifted, affinely rescaled
log-type function used for case (1c)'s interpolation window, where the boundary bound is affine in
`log|t|` rather than a pure power. The `+1` shift moves `GPL`'s centre of symmetry from `σ = 1` to
`σ = 0`, so that the window `[1/2,5/7]` lies on the increasing side of it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`, `interpG1c`,
`interpG1c_prod_α`, `interpG1c_prod_β`, `interpolated_bound_1c`. -/
noncomputable def G1shift (Q c d : ℝ) : ℂ → ℂ := fun s => (c : ℂ) * GPL Q (s + 1) + (d : ℂ)


set_option linter.unusedVariables false in
/-- **`G1shift` is strictly increasing in `σ` on `[a,b]` with `0 ≤ a`, once `|t| > Q+1`** (and `0 ≤
Q`,
`0 < c`, `0 ≤ d`) — the shift means only `a+1 ≥ 1` is needed, matching where `GPL` itself is
increasing.

### Summary of Proof
Both `‖w‖` (`GPL_mono_of_large_t`, shifted) and `Re w` (`GPL_re_mono_of_large_t`, shifted) increase
in `σ`, where `w := GPL Q(σ+1+it)`; since `c > 0`, `d ≥ 0`, `‖G1shift‖² = c²‖w‖²+2cd·Re(w)+d²`
(`normSq_c_mul_add_d`) is then a sum of nondecreasing terms in `σ`, strictly so from the `‖w‖²`
term.
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_mono_of_large_t`, `GPL_re_mono_of_large_t`,
`normSq_c_mul_add_d`.
**Used by:** `interpolated_bound_1c`, `interpolated_bound_1c_tight`. -/
theorem G1shift_mono_of_large_t (Q c d a b : ℝ) (hQ : 0 ≤ Q) (hc : 0 < c) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hQb : 0 < Q + 1 - b) 
    (h_GPL_mono_of_large_t : ∀ [LiteratureInputs] [BrentStirlingInputs] (Q a b : ℝ),
      0 ≤ Q →
        1 ≤ a →
          0 < Q + 2 - b →
            ∀ (t : ℝ),
              Q + 1 < |t| →
                StrictMonoOn (fun (σ : ℝ) ↦ ‖GPL Q ((↑σ : ℂ) + (↑t : ℂ) * Complex.I)‖) (Set.Icc a b))
    (h_GPL_re_mono_of_large_t : ∀ [LiteratureInputs] [BrentStirlingInputs] (Q a b : ℝ),
      0 ≤ Q →
        1 ≤ a →
          0 < Q + 2 - b →
            ∀ (t : ℝ),
              Q + 1 < |t| →
                StrictMonoOn (fun (σ : ℝ) ↦ (GPL Q ((↑σ : ℂ) + (↑t : ℂ) * Complex.I)).re) (Set.Icc a b))
    (h_normSq_c_mul_add_d : ∀ [LiteratureInputs] [BrentStirlingInputs] (c d : ℝ) (w : ℂ),
      ‖(↑c : ℂ) * w + (↑d : ℂ)‖ ^ 2 = c ^ 2 * ‖w‖ ^ 2 + 2 * c * d * w.re + d ^ 2)
    :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖G1shift Q c d (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t ht x hx y hy hxy
  have hmapx : x + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmapy : y + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hnormmono := h_GPL_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have hremono := h_GPL_re_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have heqx : (x:ℂ) + t * Complex.I + 1 = ((x + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have heqy : (y:ℂ) + t * Complex.I + 1 = ((y + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hvalx : G1shift Q c d (x + t * Complex.I)
      = (c:ℂ) * GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqx]
  have hvaly : G1shift Q c d (y + t * Complex.I)
      = (c:ℂ) * GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqy]
  have hwx_nn : (0:ℝ) ≤ ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ := norm_nonneg _
  have hsq : ‖G1shift Q c d (x + t * Complex.I)‖ ^ 2 < ‖G1shift Q c d (y + t * Complex.I)‖ ^ 2 := by
    rw [hvalx, hvaly, h_normSq_c_mul_add_d, h_normSq_c_mul_add_d]
    have h1 : c ^ 2 * ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2
        < c ^ 2 * ‖GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2 := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      exact pow_lt_pow_left₀ hnormmono hwx_nn (by norm_num)
    have h2 : 2 * c * d * (GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)).re
        ≤ 2 * c * d * (GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)).re := by
      rcases eq_or_lt_of_le hd with hd0 | hd0
      · simp [← hd0]
      · exact mul_le_mul_of_nonneg_left hremono.le (by positivity)
    linarith
  have hnn2 : (0:ℝ) ≤ ‖G1shift Q c d (y + t * Complex.I)‖ := norm_nonneg _
  exact lt_of_pow_lt_pow_left₀ 2 hnn2 hsq
/-! ### Fiori's Phragmén–Lindelöf theorem in the exact form applied here

`BackgroundZetaBounds`' `interpolated_bound_1a`, `_1b` and `_2` are instances of a *single*
two-point interpolation for `ζ`: a bound `A|t|^p (log|t|)^{ra}` on the line `Re s = a`, a bound
`B|t|^q (log|t|)^{rb}` on the line `Re s = b`, and the conclusion interpolating them geometrically
across the strip. Rather than re-derive that instance three times from `fiori_phragmenLindelof`
(which would mean discharging its holomorphy, conjugacy, envelope and monotonicity hypotheses
afresh each time), we record the applied form once, as `fiori_zeta_interpolation`. Case (1c)'s
boundary bound at `σ = a` has a shape this wrapper cannot express and gets its own instantiation,
`fiori_zeta_interpolation_1c`, further down. -/
