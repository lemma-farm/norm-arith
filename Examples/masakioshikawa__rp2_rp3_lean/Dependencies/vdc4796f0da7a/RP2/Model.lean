module
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.FiniteAveraging
public import Mathlib
public section
/-!
# The finite-volume RP² model and its quadrupolar observable

Spins are unit vectors, and the interaction and observable are invariant under
independent changes of sign.  Thus they descend to director spins without
choosing a global lift.  No decay theorem is assumed in this module.
-/
namespace RP2
open MeasureTheory
open scoped BigOperators InnerProductSpace
abbrev E3 := EuclideanSpace ℝ (Fin 3)
noncomputable abbrev Spin := Metric.sphere (0 : E3) 1
@[expose] noncomputable def sphereProbability : Measure Spin :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere
@[expose] instance sphereProbability_isProbability : IsProbabilityMeasure sphereProbability := by
  have hs : (volume : Measure E3).toSphere ≠ 0 := Measure.toSphere_ne_zero _
  constructor
  dsimp [sphereProbability]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_eq_zero.not.mpr hs)
    (measure_ne_top _ _)
section FiniteVolume
variable {V E : Type*} [Fintype V] [Fintype E]
abbrev Configuration (V : Type*) := V → Spin
@[expose] noncomputable def referenceLaw : Measure (Configuration V) :=
  Measure.pi (fun _ => sphereProbability)
@[expose] instance referenceLaw_isProbability : IsProbabilityMeasure (referenceLaw (V := V)) := by
  unfold referenceLaw
  infer_instance
end FiniteVolume
/-! A finite cancellation certificate. The twelve displayed transformations
are the orientation-preserving signed cyclic permutations (tetrahedral rotations).
The following polynomial identity verifies cancellation directly; no Haar
integration is needed to annihilate this observable. -/
end RP2
