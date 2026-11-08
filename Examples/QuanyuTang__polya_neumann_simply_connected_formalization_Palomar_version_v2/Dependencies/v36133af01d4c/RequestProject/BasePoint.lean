module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v36133af01d4c.RequestProject.Transport
/-!
# Change of base point and translation of the boundary curve (Lemma 10.3)

For a periodic coefficient, the solution of the linear Volterra equation can be continued
over a second period by `W(θ + L) = W(θ) W(L)`.  Consequently, starting the evolution at
the parameter `t` instead of `0` replaces the endpoint value `V = W(L)` by the conjugate
`W(t) V W(t)⁻¹`.  For the boundary transport this is the "cyclic change of base point" part
of Lemma 10.3 (and of Lemma 4.5) of the paper; translations of the curve do not change the
transport at all.  As a consequence `‖U_E - I‖` does not depend on the base point.
-/
@[expose] public section
open MeasureTheory Set
noncomputable section
namespace PolyaNeumann
variable {A : Type*} [NormedRing A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}
variable [NormedAlgebra ℝ A] [CompleteSpace A]
open scoped ComplexConjugate Real
end PolyaNeumann
end
