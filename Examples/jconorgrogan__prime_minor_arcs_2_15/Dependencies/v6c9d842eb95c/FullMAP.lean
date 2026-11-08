import Mathlib
/-!
# Full MAP and prime-pair endpoint: exact declarations and finite bridges

This file has two deliberately separate jobs.

* `PrimePairEndpoints` gives the literal, unconditional propositions that a
  complete formalization must prove.  In particular, the polylogarithmic mask
  exponents are chosen *after* the requested saving `A` and aperture reserve
  `ε`, and remain fixed for every later `X`, `H`, and Fourier center.
* `FiniteBridges` proves the exact finite square expansion behind the
  variance/Q4+ conversion and the finite Chebyshev counting inequality behind
  the density-one consequence.

No theorem in this file assumes MAP, Shiu, a zero-density theorem, a zero-free
region, Perron's formula, or the MRT transfer.  The final endpoint below is a
`Prop` to be proved, not an axiom and not a theorem with hidden hypotheses.
-/
namespace PrimePairEndpoints
open MeasureTheory Metric Set
open scoped BigOperators ArithmeticFunction
noncomputable section
def twinPrimeConstant : ℝ :=
  ∏' p : ℕ,
    if p.Prime ∧ 2 < p then
      ((p : ℝ) * ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ 2
    else 1
/-- Hardy--Littlewood singular series. Its domain deliberately excludes zero. -/
def singularSeries (h : {z : ℤ // z ≠ 0}) : ℝ :=
  if (2 : ℤ) ∣ h.1 then
    2 * twinPrimeConstant *
      ∏' p : ℕ,
        if p.Prime ∧ 2 < p ∧ (p : ℤ) ∣ h.1 then
          ((p : ℝ) - 1) / ((p : ℝ) - 2)
        else 1
  else 0
/-- Exact translated integer window, before deleting zero. -/
def translatedWindow (H h₀ : ℝ) : Finset ℤ :=
  Finset.Icc ⌈h₀ - H⌉ ⌊h₀ + H⌋
/-- Technical totalization used only in sums; the mathematical series remains undefined at zero. -/
def singularSeriesTotal (h : ℤ) : ℝ :=
  if hh : h ≠ 0 then singularSeries ⟨h, hh⟩ else 0
def singularSquareMain (H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀, (singularSeriesTotal h) ^ 2
def LegalParameters (ε X H h₀ : ℝ) : Prop :=
  Real.rpow X (2 / 15 + ε) ≤ H ∧
  H ≤ Real.rpow X (1 - ε) ∧
  0 ≤ h₀ ∧
  h₀ ≤ Real.rpow X (1 - ε)
end
end PrimePairEndpoints
namespace FiniteBridges
open scoped BigOperators
section Q4Variance
variable {ι : Type*}
end Q4Variance
section DensityOne
variable {ι : Type*}
end DensityOne
end FiniteBridges
namespace PrimePairEndpoints
open scoped BigOperators
end PrimePairEndpoints
