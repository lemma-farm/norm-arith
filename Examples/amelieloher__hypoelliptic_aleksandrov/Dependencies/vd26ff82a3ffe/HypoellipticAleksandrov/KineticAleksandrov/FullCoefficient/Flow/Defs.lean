module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The auxiliary Gaussian flow: definitions

definition the Gaussian flow. The kernel `Φ_h` is the centred Gaussian
density on phase space `y = (v, z)` with covariance `Σ_h`; it is a product of the two-dimensional
densities `φ_h(z_i, v_i)`. For `λ, h > 0` the pair density is rewritten in the form
`κ * exp (-(a u² + b u w + c w²))` with explicit coefficients, which is the form used throughout.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Real
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
