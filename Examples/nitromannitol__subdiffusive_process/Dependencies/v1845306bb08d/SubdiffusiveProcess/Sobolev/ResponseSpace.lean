module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.FiniteResponses
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Variational.SourceObjectives
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Concrete spaces and coefficients for finite responses

The space is a closed subspace of the actual distributional H1 graph,
with ordinary Poincare stated explicitly. The coefficient is an actual L∞
class bounded away from zero. No response or limiting theorem is a field.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A concrete Sobolev variation space on which ordinary Poincare holds. -/
structure ResponseSpace (Ω : Opens (SpatialCoordinates d)) where
  space : Submodule ℝ (SobolevData Ω)
  le_weak : space ≤ weakSobolevGraph Ω
  closed : IsClosed (space : Set (SobolevData Ω))
  poincare : ∃ K : ℝ≥0, ∀ z : space,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient space z‖
/-- Killed variations use the previously constructed H1_0 completion. -/
def killedResponseSpace (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨killedSobolevGraph Ω, killedSobolevGraph_le_weakSobolevGraph,
    isClosed_killedSobolevGraph, hP⟩
/-- Neumann variations use the actual mean-zero weak-gradient graph. -/
def meanZeroResponseSpace [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨meanZeroSobolevGraph Ω, inf_le_left, isClosed_meanZeroSobolevGraph, hP⟩
/-- Actual bounded scalar coefficients with a uniform positive lower bound. -/
def PositiveCoefficient (Ω : Opens (SpatialCoordinates d)) :=
  {a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) //
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x}
/-- The bilinear energy on the concrete Sobolev variation space. -/
def responseForm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    S.space →L[ℝ] S.space →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (subspaceGradient S.space) (subspaceGradient S.space)
theorem existsUnique_responseForm_solution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : ∃! u : S.space, ∀ v, responseForm S a u v = L v := by
  obtain ⟨K, hP⟩ := S.poincare
  obtain ⟨c, hc, ha⟩ := a.property
  exact existsUnique_gradient_subspace_solution S.space S.closed K hP a.val hc ha L
/-- The unique weak source solution; no fallback value is used. -/
def responseSolution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    S.space := Classical.choose (existsUnique_responseForm_solution S a L)
/-- Defining equation of the selected unique source solution. -/
theorem responseSolution_spec (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (v : S.space) :
    responseForm S a (responseSolution S a L) v = L v :=
  (Classical.choose_spec (existsUnique_responseForm_solution S a L)).1 v
def inverseResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) : ℝ :=
  responseForm S a (responseSolution S a L) (responseSolution S a L)
/-- The inverse response also equals the load evaluated at its solution. -/
theorem inverseResponse_eq_load (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : inverseResponse S a L = L (responseSolution S a L) :=
  responseSolution_spec S a L _
end SubdiffusiveProcess
