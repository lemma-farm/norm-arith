module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi
/-- Appendix `a.besov`: for `t > 0`, the Gaussian
`G_t(x) = (4πt)^{-d/2} exp(-|x|² / (4t))`, `x ∈ ℝ^d`, with `|x|² = vecNormSq x`. -/
noncomputable def gaussianKernel {d : ℕ} (t : ℝ) (_ht : 0 < t) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(vecNormSq x) / (4 * t))
end CoarseDeGiorgi
