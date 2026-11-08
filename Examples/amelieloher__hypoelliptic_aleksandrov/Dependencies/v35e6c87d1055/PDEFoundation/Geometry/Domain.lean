module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.PDEFoundation.Ambient.EuclideanNorm
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.PDEFoundation.Geometry.Affine
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Quantitative domain predicates

The compatibility boundedness predicate is retained alongside an explicit
Euclidean-diameter bound for quantitative Sobolev estimates.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
/-- Coordinatewise boundedness, compatible with the existing LIH API. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R
/-- The minimal measurable bounded domain class used by Sobolev integration. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U
/-- Every pair of points in `U` is at Euclidean distance at most `D`. -/
def HasEuclideanDiameterLE {d : ℕ}
    (U : Set (Vec d)) (D : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    vecEuclideanNorm (x - y) ≤ D
namespace IsSobolevRegularDomain
theorem measurableSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1
end IsSobolevRegularDomain
namespace HasEuclideanDiameterLE
theorem mono {d : ℕ} {U V : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (hVU : V ⊆ U) :
    HasEuclideanDiameterLE V D := by
  intro x hx y hy
  exact hU (hVU hx) (hVU hy)
end HasEuclideanDiameterLE
end PDE
