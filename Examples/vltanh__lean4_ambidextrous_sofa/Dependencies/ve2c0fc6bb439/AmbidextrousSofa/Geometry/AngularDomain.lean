module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.Barriers
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.Reflection
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Continuous passages and their complete angular constraints

The intermediate value theorem, rather than monotonicity of a motion, supplies
every intervening angle. A genuine terminal angle in `(0, π/2]` retains its
outgoing whole-body support wall. A visited full quarter turn uses the incoming
unit strip for the endpoint wall. Reflection turns an independent upper passage
into a lower passage by an explicit continuous rigid motion.

These results do not claim that every original passage has one of the stated
angular reaches. The wrong-way exclusion and the reach dichotomy are separate
remaining steps of the original-domain reduction.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
/-- All actual frame constraints, together with the whole outgoing support wall. -/
structure AngularConstraints (S K : Set Plane) (α : ℝ) : Prop where
  angle_pos : 0 < α
  angle_le : α ≤ Real.pi / 2
  inside : ∀ θ ∈ Ioo 0 α, S ⊆ canonicalHall K (unitNormal θ) (companionNormal θ)
  terminal : ∀ p ∈ S, support K (unitNormal α) - 1 ≤ coordDot p (unitNormal α)
end AmbidextrousSofa
