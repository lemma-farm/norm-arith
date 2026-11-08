module
public import Mathlib.Analysis.Calculus.Rademacher
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.BasePoint
/-!
# Reparametrization invariance of the transport (Lemma 10.3, first assertion)

An orientation-preserving Lipschitz change of parameter `τ` with `τ 0 = 0`, `τ L = L`
does not change the endpoint value `V_E = W_E(L)` of the transport.  More precisely, if `W`
is the transport of `γ` then `W ∘ τ` is the transport of `γ ∘ τ`.

The proof follows the paper: the absolutely continuous chain rule and uniqueness.  The only
measure-theoretic input beyond Mathlib's one-dimensional area formula is that a monotone
function has vanishing derivative almost everywhere on the preimage of a null set
(`ae_deriv_eq_zero_of_preimage_null`).
-/
@[expose] public section
open MeasureTheory Set Filter Asymptotics
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L L' : ℝ} {W : ℝ → A} {τ : ℝ → ℝ}
end PolyaNeumann
end
