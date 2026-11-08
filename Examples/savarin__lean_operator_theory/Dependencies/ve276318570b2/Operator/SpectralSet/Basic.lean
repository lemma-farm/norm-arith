/-
# Polynomial spectral sets — definitions (L2.1)

Defines `polynomialSupNorm`, `IsKPolynomialSpectralSet`, and `IsPolynomialSpectralSet`.
These are *polynomial* spectral sets (norm bound on `Polynomial.aeval`).
-/
import Mathlib
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖
