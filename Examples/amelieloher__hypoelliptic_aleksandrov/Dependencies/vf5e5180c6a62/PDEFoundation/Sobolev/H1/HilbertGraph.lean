module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.H1.Graph
public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hilbert realization of the complete `H¹` graph

`H1Graph U` deliberately inherits the maximum norm on the product used by the
general-`p` graph.  At `p = 2`, Lax--Milgram and Riesz representation instead
need the equivalent `ℓ²` product norm.  This file pulls the same closed graph
back through `WithLp.prodContinuousLinearEquiv`; it does not conflate the two
norms.
-/
@[expose] public section
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace PDE
/-- The `ℓ²`-normed product ambient for the `p = 2` weak-gradient graph. -/
abbrev H1HilbertAmbient {d : ℕ} (U : Set (Vec d)) :=
  WithLp 2
    (ScalarLp U (2 : ℝ≥0∞) × HilbertVectorLp U (2 : ℝ≥0∞))
/-- The standard continuous linear equivalence from the `ℓ²` product
realization to the ordinary product carrier. -/
abbrev h1HilbertAmbientEquiv {d : ℕ} (U : Set (Vec d)) :
    H1HilbertAmbient U ≃L[ℝ]
      WeakGradientLpPair U (2 : ℝ≥0∞) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ
    (ScalarLp U (2 : ℝ≥0∞))
    (HilbertVectorLp U (2 : ℝ≥0∞))
/-- The same weak-gradient graph, pulled back to the Hilbert product norm. -/
abbrev h1HilbertClosedSubmodule {d : ℕ} (U : Set (Vec d)) :
    ClosedSubmodule ℝ (H1HilbertAmbient U) :=
  (weakGradientGraph U (2 : ℝ≥0∞)).comap
    (h1HilbertAmbientEquiv U).toContinuousLinearMap
/-- Submodule view used to inherit the Hilbert-space instances. -/
abbrev h1HilbertSubmodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (H1HilbertAmbient U) :=
  (h1HilbertClosedSubmodule U).toSubmodule
/-- The complete Hilbert realization of `H1Graph U`. -/
abbrev H1HilbertGraph {d : ℕ} (U : Set (Vec d)) :=
  ↥(h1HilbertSubmodule U)
namespace H1HilbertGraph
variable {d : ℕ} {U : Set (Vec d)}
noncomputable instance : SeminormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1HilbertSubmodule U))
noncomputable instance : NormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedAddCommGroup (h1HilbertSubmodule U))
noncomputable instance : NormedSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedSpace ℝ (h1HilbertSubmodule U))
noncomputable instance : InnerProductSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (InnerProductSpace ℝ (h1HilbertSubmodule U))
noncomputable instance : CompleteSpace (H1HilbertGraph U) := by
  exact (h1HilbertClosedSubmodule U).isClosed.completeSpace_coe
def valueCLM :
    H1HilbertGraph U →L[ℝ] ScalarLp U (2 : ℝ≥0∞) :=
  (WithLp.fstL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL
end H1HilbertGraph
end PDE
