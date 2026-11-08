module
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.RotationGeometry
public import Examples.masakioshikawa__rp2_rp3_lean.Dependencies.vdc4796f0da7a.RP2.Calculus
public import Mathlib
public section
/-!
# Pinned quadratic-spin Gibbs systems

Gauge transformations and their reference-measure proofs are adapted from
OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The interaction here is the squared scalar product. Its derivative jets are
constructed by the product rule, rather than the linear-energy formulas in
that source.
-/
namespace RP2.Quadratic
universe uV uE
noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
@[expose] def siteReference (p : Option (RP2.Spin)) : Measure (RP2.Spin) :=
  match p with
  | none => sphereProbability
  | some s => Measure.dirac s
@[expose] instance siteReference_isProbability (p : Option (RP2.Spin)) :
    IsProbabilityMeasure (siteReference p) := by
  cases p <;> dsimp [siteReference] <;> infer_instance
structure SpinSystem (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  strength : E → ℝ
  pin : V → Option (RP2.Spin)
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
@[expose] def reference (S : SpinSystem V E) : Measure (V → RP2.Spin) :=
  Measure.pi (fun x => siteReference (S.pin x))
@[expose] instance reference_isProbability (S : SpinSystem V E) :
    IsProbabilityMeasure S.reference := by
  unfold reference
  infer_instance
end SpinSystem
end
end RP2.Quadratic
