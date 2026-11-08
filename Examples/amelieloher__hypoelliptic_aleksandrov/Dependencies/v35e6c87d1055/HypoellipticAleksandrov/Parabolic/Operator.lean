module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Ambient.MatrixContraction
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Coefficients.Ellipticity
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.Derivatives
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The forward parabolic operator

This module defines the time--velocity operator with sign
`∂ₜ u - A : Dᵥ² u` and its transparent pointwise subsolution predicate.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
/-- The forward parabolic operator `∂ₜ u - A : Dᵥ² u`. -/
def parabolicOperator {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z)
def IsParabolicSubsolutionOn {d : ℕ} (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ s, parabolicOperator A u z ≤ f z
namespace IsParabolicSubsolutionOn
/-- A subsolution inequality holds at every point of its defining set. -/
theorem le {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {s : Set (TimeVelocity d)} (h : IsParabolicSubsolutionOn A f u s)
    {z : TimeVelocity d} (hz : z ∈ s) :
    parabolicOperator A u z ≤ f z :=
  h z hz
end IsParabolicSubsolutionOn
end HypoellipticAleksandrov.Parabolic
