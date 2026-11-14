module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic.Linarith

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4866300f0c0a.SubdiffusiveProcess.Sobolev.WeakGradient ====
public section
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
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end
end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4866300f0c0a.SubdiffusiveProcess.VariationalResponses.LimitForm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
/-- `E(u)` of `eq:mfd-18`:
the dual energy of the killed inverse `G`. -/
def limitFormEnergy (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : EReal :=
  ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_f4cffad76385215fabd6_LimitFormUniqueness ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! A positive symmetric killed inverse is determined by its dual energy and
finite-energy domain. No existence or convergence of an inverse is asserted. -/
open MeasureTheory Set TopologicalSpace
namespace SubdiffusiveProcess
noncomputable section
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
/-- The dual energy at an image vector equals its original quadratic pairing. -/
theorem limitFormEnergy_apply_eq
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (x : DomainL2 Q) :
    limitFormEnergy G (G x) = ((inner ℝ x (G x) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro f
    apply EReal.coe_le_coe_iff.mpr
    have h := hp (f - x)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h
    rw [hs x f] at h
    linarith only [h]
  · apply le_iSup_of_le x
    apply EReal.coe_le_coe_iff.mpr
    linarith only []
end
end SubdiffusiveProcess
