module
public import Examples.na0b__infharmonic_lean.Dependencies.ve088d47e3348.InfHarmonic.Preamble
set_option autoImplicit false
@[expose] public section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The sup-convolution `φ^ε z = sup_w (φ w - ‖z - w‖² / (2 ε))`. -/
noncomputable def SupConvolution (ε : ℝ) (φ : E → ℝ) (z : E) : ℝ :=
  sSup (Set.range (fun w : E => φ w - ‖z - w‖ ^ 2 / (2 * ε)))
