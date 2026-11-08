module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.SecondOrder
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomially growing coefficient families

For the Gaussian exponential `G_θ = gaussExp θ₁ θ₂ θ₃` every iterated coordinate derivative has
the form `P_θ * G_θ` where `P_θ` is a polynomial of degree at most the order. To obtain bounds
that are uniform in the coefficient triple `θ` (on bounded sets, hence on compact `h`-intervals
for the flow), we track a family `θ ↦ P_θ` in the predicate `PG k S`: degree `≤ k`, with growth
constant uniform over `Coef S = {θ | |θᵢ| ≤ S}`. This realizes the polynomial structure behind the
derivative bounds of the Gaussian flow.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The parameter triple `(a, b, c)` of the quadratic form. -/
abbrev Theta : Type := ℝ × ℝ × ℝ
/-- The coefficient triples bounded by `S`. -/
def Coef (S : ℝ) : Set Theta := {θ | |θ.1| ≤ S ∧ |θ.2.1| ≤ S ∧ |θ.2.2| ≤ S}
/-- The gradient `∂_δ Q_θ` of the quadratic form, as a function of the triple. -/
def genT (θ : Theta) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) : ℝ :=
  gen θ.1 θ.2.1 θ.2.2 δ y
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
