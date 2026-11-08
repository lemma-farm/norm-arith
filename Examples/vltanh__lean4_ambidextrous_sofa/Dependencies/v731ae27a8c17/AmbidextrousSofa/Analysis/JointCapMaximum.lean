module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.PartialCapContinuity
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.GlobalCapMaximum
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual maxima over caps and terminal angles

The terminal parameter varies over the entire closed interval from `π/4`
to `π/2`. Joint continuity supplies a maximum in a compact box. The same
width bound used for the full problem applies to every one of these angles,
so horizontal translation turns that boxed maximum into a maximum over all
actual downward caps. A second compact maximum selects the largest terminal
angle among global maxima.

The chord and height operations preserve the chosen angle and the attained
score. In particular, the largest-angle choice survives canonicalization.
No sharp upper bound or terminal variational law is assumed here.
-/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
/-- A maximum over every actual cap and every allowed terminal angle. -/
def IsJointCapMaximizer (U : Set Plane) (α : ℝ) : Prop :=
  IsDownwardCap U ∧ α ∈ Icc (Real.pi / 4) (Real.pi / 2) ∧
    ∀ V : Set Plane, ∀ β : ℝ, IsDownwardCap V →
      β ∈ Icc (Real.pi / 4) (Real.pi / 2) → capScore V β ≤ capScore U α
namespace IsJointCapMaximizer
variable {U V : Set Plane} {α β : ℝ} (hU : IsJointCapMaximizer U α)
include hU
theorem angle_mem : α ∈ Icc (Real.pi / 4) (Real.pi / 2) := hU.2.1
theorem angle_pos : 0 < α := hU.angle_mem.1.trans_lt' (by positivity)
end IsJointCapMaximizer
end AmbidextrousSofa
