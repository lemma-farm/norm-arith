-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.Homogenization.Geometry.OriginCubeBoundaryPush
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.Homogenization.Geometry.Translation
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
/-!
# Bounded Open Convex Domains

This file bridges the repository's custom bounded-domain predicate
`IsBoundedDomain` with Mathlib's bounded-set API, records the resulting finite
measure consequences for Lebesgue measure, and packages the domain class
`IsOpenBoundedConvexDomain`.

The intended analytic use is to give future Sobolev/Hodge results a stable
geometric target class that already contains the open cubes and metric balls
used downstream.
-/
theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg (le_of_lt hRpos)).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U
namespace IsOpenBoundedConvexDomain
end IsOpenBoundedConvexDomain
namespace IsSobolevRegularDomain
end IsSobolevRegularDomain
end Homogenization
