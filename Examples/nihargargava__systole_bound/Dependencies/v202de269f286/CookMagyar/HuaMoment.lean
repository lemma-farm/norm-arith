module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.PrimePowerAnalytic
@[expose] public section
open MeasureTheory
open scoped ArithmeticFunction BigOperators ComplexConjugate
namespace SystolicGrowth
namespace CookMagyarCircle
/-! # Exact interpretation of the cubic eighth moment

The analytic Hua estimate bounds an eighth moment.  Before any estimate is
made, Fourier orthogonality identifies that moment exactly with a weighted
additive energy: two four-tuples having the same value of
`∑ (x³-x)`.  This file proves that identity.
-/
@[simp] theorem conj_addChar (alpha : ℝ) (k : ℕ) :
    conj (addChar alpha k) = negAddChar alpha k := by
  unfold addChar negAddChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_natCast, Complex.conj_ofReal,
    Complex.conj_I]
  ring
end CookMagyarCircle
end SystolicGrowth
