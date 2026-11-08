module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.PDEFoundation.Sobolev.H1.HilbertGraph
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.PDEFoundation.Sobolev.H1.ZeroBoundary
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hilbert realization of spatial `H¹₀`

This module defines spatial `H¹₀(Ω)` as the closure in the Hilbert realization
of the weak-gradient graph of the image of actual bundled smooth compactly
supported test functions.  It then proves that this carrier agrees with the
existing maximum-norm graph realization from `PDEFoundation`.

No density result for the value map into spatial `L²` is asserted here.
-/
@[expose] public section
open Filter
open scoped ENNReal RealInnerProductSpace Topology
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
/-- The continuous linear equivalence from the Hilbert-norm weak-gradient
graph to the corresponding maximum-norm graph. -/
noncomputable def h1HilbertGraphContinuousLinearEquiv
    (Ω : Set (PDE.Vec d)) :
    PDE.H1HilbertGraph Ω ≃L[ℝ] PDE.H1Graph Ω :=
  (PDE.h1HilbertAmbientEquiv Ω).ofSubmodule'
    (PDE.weakGradientGraph Ω (2 : ℝ≥0∞)).toSubmodule
noncomputable def smoothCompactlySupportedH1HilbertGraphLinearMap
    (hΩ : IsOpen Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.H1HilbertGraph Ω :=
  (h1HilbertGraphContinuousLinearEquiv Ω).symm.toLinearMap.comp
    (PDE.smoothCompactlySupportedW1pGraphLinearMap
      (p := (2 : ℝ≥0∞)) hΩ)
/-- The submodule of Hilbert-graph points coming from actual bundled smooth
compactly supported test functions. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphSubmodule
    (hΩ : IsOpen Ω) :
    Submodule ℝ (PDE.H1HilbertGraph Ω) :=
  LinearMap.range (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ)
/-- The closed Hilbert-graph submodule defining spatial `H¹₀`. -/
noncomputable def h10HilbertGraphClosedSubmodule
    (hΩ : IsOpen Ω) :
    ClosedSubmodule ℝ (PDE.H1HilbertGraph Ω) :=
  (smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).closure
/-- The complete Hilbert realization of spatial `H¹₀(Ω)`. -/
noncomputable abbrev H10HilbertGraph (hΩ : IsOpen Ω) :=
  ↥((h10HilbertGraphClosedSubmodule hΩ).toSubmodule)
noncomputable instance (hΩ : IsOpen Ω) :
    SeminormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (SeminormedAddCommGroup
      ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedAddCommGroup ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    NormedSpace ℝ (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedSpace ℝ ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    InnerProductSpace ℝ (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (InnerProductSpace ℝ
      ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    CompleteSpace (H10HilbertGraph hΩ) :=
  (h10HilbertGraphClosedSubmodule hΩ).isClosed.completeSpace_coe
/-- The continuous scalar-value map from spatial `H¹₀` to spatial `L²`. -/
noncomputable def valueCLM (hΩ : IsOpen Ω) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  PDE.H1HilbertGraph.valueCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL
end HypoellipticAleksandrov.Parabolic.Dirichlet
