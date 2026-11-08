module
public import Mathlib
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
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
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section
abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
abbrev DomainL2 {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  Lp ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
abbrev SobolevData {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  DomainL2 Ω × (Fin d → DomainL2 Ω)
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A smooth compactly supported test, as an actual scalar L2 equivalence class. -/
noncomputable def testL2 (φ : 𝓓(Ω, ℝ)) : DomainL2 Ω :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
/-- The coordinate derivative of a test is also an actual L2 function. -/
noncomputable def testPartialL2 (φ : 𝓓(Ω, ℝ)) (i : Fin d) : DomainL2 Ω :=
  ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1))).toLp
    (fun x => fderiv ℝ φ x (Pi.single i 1))
noncomputable def weakGradientTest (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    SobolevData Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (testL2 φ)).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))) +
  ((innerSL ℝ (testPartialL2 φ i)).comp (ContinuousLinearMap.fst ℝ _ _))
/-- The graph of weak first derivatives on the open domain. -/
noncomputable def weakSobolevGraph (Ω : Opens (SpatialCoordinates d)) :
    Submodule ℝ (SobolevData Ω) :=
  ⨅ (φ : 𝓓(Ω, ℝ)) (i : Fin d), LinearMap.ker (weakGradientTest φ i).toLinearMap
end
end SubdiffusiveProcess
