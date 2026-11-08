module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SpinGlass.SKModel
public import Mathlib
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Integration
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
/-!
# Permanent support for the independent endpoint

This module contains the Gaussian-law, reference-field, and product-spin identities used by
the independent endpoint of the generalized Latała argument.
-/
open MeasureTheory ProbabilityTheory Real BigOperators
open PhysLean.Probability.GaussianIBP
open scoped ENNReal NNReal
namespace SpinGlass.GeneralizedLatala
variable {Ω H : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
end SpinGlass.GeneralizedLatala
