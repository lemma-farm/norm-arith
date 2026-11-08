/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
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
noncomputable def Nrect (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} u
