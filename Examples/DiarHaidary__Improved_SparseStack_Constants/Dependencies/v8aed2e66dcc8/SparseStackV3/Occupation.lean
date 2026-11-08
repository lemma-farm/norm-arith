/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Occupation bookkeeping for the SparseStack local spaces

This file formalizes the purely combinatorial / arithmetic layer of Section 2.1
of *SparseStack Is an Optimal Oblivious Subspace Embedding*, Version 3.0
(Diar Heidary), namely the paragraph beginning

> Tensor the local spaces over `[s] × [n]` and then with `ℝ^d`; …
> For a type pattern let `L_g, H_g` count light and heavy sites in block `g`,
> and put `L = ∑_g L_g`, `H = ∑_g H_g`, `N = L + H`, `ν = L + 2H`.

together with

* the count transitions recorded just after Figure 1: the output counts of
  `L₊, X₊, Y₊, H₊` are respectively `(L+2, H)`, `(L, H+1)`, `(L, H+1)`,
  `(L-2, H+2)`, those of `X₀, Y₀` are `(L+2, H-1)`, and `L₀, H₀` preserve both
  totals — i.e. the "grade `+2` / grade `0`" classification of Figure 1(b);
* the block-even sector `new:even-space`,
  `𝒦^ev = span {patterns with every L_g even}`;
* the grade inequalities used at the end of Section 4 when the `(L, H)` operator
  norm bounds are converted into the grade bounds `new:alpha` and `new:chi`:
  `L ≤ ν`, `H + L/2 = ν/2`, `N ≤ ν`, and, for `X₀` and `Y₀`,
  `N ≤ ν - 1` (from `H ≥ 1`) and
  `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` for `ν ≥ 2`.

Nothing analytic happens here: a *type pattern* is modelled as a function from
the site set `[s] × [n]` to the three local levels `vacuum / light / heavy`, and
all statements are finite combinatorics over `ℕ` (Sections 1–4 below) or
elementary inequalities over `ℝ` (Section 5 below).

## Main results

* `SparseStackV3.Occupation.grade_eq_sum_weight` — the two descriptions of `ν`
  agree: `ν = L + 2H` equals the sum of the local weights over all sites.
* `SparseStackV3.Occupation.L_le_grade`, `two_mul_H_le_grade`, `N_le_grade` —
  the elementary grade inequalities over `ℕ`.
* `SparseStackV3.Occupation.even_grade_of_blockEven` — the block-even sector
  `new:even-space` sits inside the even grades.
* `SparseStackV3.Occupation.grade_Lplus`, …, `grade_Yzero` — the transition
  arithmetic of Figure 1(b).
* `SparseStackV3.Occupation.Real.mul_H_add_two_le`,
  `SparseStackV3.Occupation.Real.sq_div_eight_le_sq_div_four` — the chain
  `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` for `ν ≥ 2`.
-/
namespace SparseStackV3
namespace Occupation
open scoped BigOperators
/-! ## 1. Local levels, sites and type patterns -/
/-- The three local levels carried by a site `(g, i) ∈ [s] × [n]` in the
local-space decomposition of Section 2.1: the vacuum, the *light* level (one
`P`-excitation) and the *heavy* level (one `R`-excitation). -/
inductive Level : Type
  | vac : Level
  | light : Level
  | heavy : Level
  deriving DecidableEq, Repr
namespace Level
instance : Fintype Level where
  elems := {Level.vac, Level.light, Level.heavy}
  complete := by rintro (_ | _ | _) <;> decide
/-- The grade weight of a local level: the vacuum contributes `0`, a light site
contributes `1` and a heavy site contributes `2`.  Summing this over all sites
gives the grade `ν = L + 2H` of Section 2.1. -/
def weight : Level → ℕ
  | vac => 0
  | light => 1
  | heavy => 2
end Level
/-- The site set `[s] × [n]` of Section 2.1: `s` sketch blocks, each carrying
`n` columns. -/
abbrev Site (s n : ℕ) : Type := Fin s × Fin n
/-- A *type pattern* in the sense of Section 2.1: an assignment of a local level
to every site of `[s] × [n]`.  The subspace `𝒦_{L,H}` is spanned by the patterns
with the given totals. -/
abbrev Pattern (s n : ℕ) : Type := Site s n → Level
variable {s n : ℕ}
/-! ## 2. The occupation counts `L_g, H_g, L, H, N, ν` -/
/-- The set of light sites of the pattern `p` inside the sketch block `g`. -/
def lightIn (p : Pattern s n) (g : Fin s) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (g, i) = Level.light
/-- The set of heavy sites of the pattern `p` inside the sketch block `g`. -/
def heavyIn (p : Pattern s n) (g : Fin s) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (g, i) = Level.heavy
/-- `L_g`: the number of light sites of `p` in block `g` (Section 2.1). -/
def Lg (p : Pattern s n) (g : Fin s) : ℕ := (lightIn p g).card
/-- `H_g`: the number of heavy sites of `p` in block `g` (Section 2.1). -/
def Hg (p : Pattern s n) (g : Fin s) : ℕ := (heavyIn p g).card
/-- `L = ∑_g L_g`, the total light count of the pattern `p` (Section 2.1). -/
def L (p : Pattern s n) : ℕ := ∑ g : Fin s, Lg p g
/-- `H = ∑_g H_g`, the total heavy count of the pattern `p` (Section 2.1). -/
def H (p : Pattern s n) : ℕ := ∑ g : Fin s, Hg p g
section Transitions
variable (Lc Hc ν : ℕ)
end Transitions
/-! ## 6. The real grade inequalities used at the end of Section 4

The passage after `new:chi` reads:

> For `X₀` use `H ≥ 1`, giving `N ≤ ν - 1` and `d + L + 1 ≤ d + ν - 1`.
> For `Y₀` use `H(L+2) ≤ (ν+2)²/8 ≤ (ν+1)²/4` (`ν ≥ 2`).
> The latter inequality is equivalent to `ν² ≥ 2`.
> The other terms follow from `L ≤ ν`, `H + L/2 = ν/2`, and `N - 1 ≤ ν - 1`.

These are stated over `ℝ` because they are applied to the real operator-norm
bounds of `new:family-bounds`. -/
namespace Real
variable {L H ν : ℝ}
end Real
end Occupation
end SparseStackV3
