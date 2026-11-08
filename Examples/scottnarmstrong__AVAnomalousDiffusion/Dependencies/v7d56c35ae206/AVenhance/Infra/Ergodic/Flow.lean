-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Ergodic.Periodic
public import Mathlib
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Periodic volume-preserving diffeomorphisms -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory
open scoped Pointwise
noncomputable section
/-- A smooth diffeomorphism of `Vec d` whose lift commutes with integer
lattice translations and which preserves Lebesgue measure. -/
structure PeriodicVolumePreservingDiffeomorphism (d : ℕ) where
  toFun : Homogenization.Vec d → Homogenization.Vec d
  invFun : Homogenization.Vec d → Homogenization.Vec d
  contDiff_toFun : ContDiff ℝ ∞ toFun
  contDiff_invFun : ContDiff ℝ ∞ invFun
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  lattice_equivariant : ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    toFun (x + latticeVector k) = toFun x + latticeVector k
  measurePreserving : MeasurePreserving toFun volume volume
instance {d : ℕ} : CoeFun (PeriodicVolumePreservingDiffeomorphism d)
    (fun _ => Homogenization.Vec d → Homogenization.Vec d) :=
  ⟨PeriodicVolumePreservingDiffeomorphism.toFun⟩
noncomputable def Flow.negativeCoordinateBasis (d : ℕ) :
    Module.Basis (Fin d) ℝ (Homogenization.Vec d) :=
  (Pi.basisFun ℝ (Fin d)).map (LinearEquiv.neg ℝ)
def Flow.flowLattice (d : ℕ) : AddSubgroup (Homogenization.Vec d) :=
  (Submodule.span ℤ (Set.range (Flow.negativeCoordinateBasis d))).toAddSubgroup
noncomputable def Flow.flowLatticeCoordinates {d : ℕ} (g : Flow.flowLattice d) :
    Fin d → ℤ := fun i => Classical.choose
      (((Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _).mp g.property i)
theorem Flow.flowLatticeCoordinates_spec {d : ℕ} (g : Flow.flowLattice d) (i : Fin d) :
    ((Flow.flowLatticeCoordinates g i : ℤ) : ℝ) =
      ((Flow.negativeCoordinateBasis d).repr (g : Homogenization.Vec d)) i :=
  Classical.choose_spec
    (((Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _).mp g.property i)
theorem Flow.flowLattice_countable (d : ℕ) : Countable (Flow.flowLattice d) := by
  have hinj : Function.Injective (Flow.flowLatticeCoordinates (d := d)) := by
    intro g h hgh
    apply Subtype.ext
    apply (Flow.negativeCoordinateBasis d).repr.injective
    ext i
    rw [← Flow.flowLatticeCoordinates_spec g i, ← Flow.flowLatticeCoordinates_spec h i, hgh]
  exact hinj.countable
private instance {d : ℕ} : Countable (Flow.flowLattice d) := Flow.flowLattice_countable d
end
end AVenhance.Infra.Ergodic
