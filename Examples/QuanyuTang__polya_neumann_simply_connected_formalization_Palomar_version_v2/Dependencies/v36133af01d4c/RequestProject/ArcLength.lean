module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v36133af01d4c.RequestProject.Reparam
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v36133af01d4c.RequestProject.CurveContinuity
/-!
# Rescaled-arclength parametrizations of Lipschitz Jordan curves

A Lipschitz, `2π`-periodic curve `γ` which is injective on `[0, 2π)` can be reparametrized by
rescaled arclength: there is a curve `γ̃` with the same image of `[0, 2π]`, again Lipschitz,
`2π`-periodic and injective on `[0, 2π)`, with `‖γ̃'‖` equal to a positive constant almost
everywhere, with the same signed-area integral `∫₀^{2π} Im(conj γ · γ')`, and with
`γ = γ̃ ∘ τ` for a monotone Lipschitz `τ` fixing `0` and `2π` (`exists_constSpeed_reparam`).
Reversing the direction changes the sign of this integral
(`exists_reverse_param`).

These are the analytic steps that turn a Lipschitz Jordan parametrization of the boundary into
a positively oriented rescaled-arclength parametrization (Definition 10.1 of the paper).
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
section ArcLen
variable {γ : ℝ → ℂ} {K : NNReal}
end ArcLen
end PolyaNeumann
