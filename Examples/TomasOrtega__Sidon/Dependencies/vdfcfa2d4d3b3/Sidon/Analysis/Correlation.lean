module
public import Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Analysis.FiniteFourier
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Finite correlations and integer translations -/
noncomputable section
open scoped ComplexConjugate
namespace Sidon
def correlation (f g : ℤ →₀ ℂ) (h : ℤ) : ℂ :=
  f.sum fun x c => c * conj (g (x + h))
end Sidon
