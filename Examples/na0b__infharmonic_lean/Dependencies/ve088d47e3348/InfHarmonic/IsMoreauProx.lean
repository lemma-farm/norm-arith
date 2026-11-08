module
public import Examples.na0b__infharmonic_lean.Dependencies.ve088d47e3348.InfHarmonic.Preamble
set_option autoImplicit false
@[expose] public section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- `u` is a proximal map for `ψ`: for every `y`, the point `u y` minimizes
`x ↦ ψ x + ‖x - y‖² / 2` over `E`. -/
def IsMoreauProx (ψ : E → ℝ) (u : E → E) : Prop :=
  ∀ y x : E, ψ (u y) + ‖u y - y‖ ^ 2 / 2 ≤ ψ x + ‖x - y‖ ^ 2 / 2
