-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Ambient.Basic
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R
/--
Working domain-regularity predicate for the current Sobolev layer.

At this stage of the development, the reusable geometric input needed by the
mean-zero and affine-average arguments is exactly measurability together with
the repository's bounded-domain predicate.
-/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U
namespace IsSobolevRegularDomain
end IsSobolevRegularDomain
end Homogenization
