module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PhaseProduct
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Mass and supremum of the Gaussian flow kernel

The Gaussian flow estimates: positivity, total mass one and the
supremum bound for `Φ_h`, derived from the Gaussian integral of the exponential
`gaussExp a b c = exp (-(∑ᵢ a zᵢ² + b zᵢ vᵢ + c vᵢ²))`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Real MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
