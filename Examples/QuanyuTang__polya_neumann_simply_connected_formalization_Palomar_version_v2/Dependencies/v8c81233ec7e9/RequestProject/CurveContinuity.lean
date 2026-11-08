module
public import Mathlib.Analysis.Calculus.Rademacher
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Observation
/-!
# Continuity of the monodromy under uniform convergence of curves (Lemma 10.6)

If closed Lipschitz curves `γₙ` converge uniformly to a closed Lipschitz curve `γ` with
uniformly bounded lengths `∫₀^L |γₙ'|`, and `Eₙ → E`, then `U_{γₙ}(Eₙ) → U_γ(E)` in operator
norm.

The proof is the paper's: with `Fₙ` a primitive of `C - Cₙ` vanishing at both endpoints,
the variation identity and an integration by parts give
`Vₙ^* V - I = ∫₀^L Wₙ^* (Cₙ Fₙ - Fₙ C) W`, whence
`‖Vₙ^* V - I‖ ≤ ‖Fₙ‖_∞ ∫₀^L (‖Cₙ‖ + ‖C‖) → 0`.
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
section Generic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [StarModule ℝ A] [NormedStarGroup A]
variable {C C' : ℝ → A} {M M' L : ℝ} {W W' F : ℝ → A}
end Generic
/-! ### The boundary transport -/
end PolyaNeumann
end
