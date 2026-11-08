module
public import Examples.na0b__infharmonic_lean.Dependencies.ve088d47e3348.InfHarmonic.Preamble
set_option autoImplicit false
@[expose] public section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- `φ` is `lam`-semiconvex on `Ω`: the quadratic perturbation
`z ↦ φ z + lam ‖z‖² / 2` is convex on `Ω`. -/
def SemiconvexOn (lam : ℝ) (Ω : Set E) (φ : E → ℝ) : Prop :=
  ConvexOn ℝ Ω (fun z => φ z + lam * ‖z‖ ^ 2 / 2)
