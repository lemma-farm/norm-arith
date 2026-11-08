module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v081b08e93cc6.HypoellipticAleksandrov.Coefficients.Ellipticity
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v081b08e93cc6.HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Matrix lemmas for the smoothing package

Elementary facts on real symmetric matrices with two-sided Loewner bounds used in
the smoothing estimates: the upper Loewner bound from a quadratic
form bound, the operator-type bound `|B x|² ≤ Λ² |x|²`, and the Frobenius bound
`∑ᵢⱼ Bᵢⱼ² ≤ d Λ²`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
