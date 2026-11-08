module
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.TietzeExtension
@[expose] public section
/-!
# Character averages and continuous orbit detectors

The measure below is the actual normalized Haar measure on a compact group. Averaging
with a circle character gives a continuous equivariant complex-valued function. A
character trivial on a point stabilizer descends to the compact orbit; Tietze extension
then supplies an averaging input whose average equals one at that point.

These are topological prerequisites for the detector in Section 7 of `fullHS_final.md`.
They do not assume the proposed controlled realization or assert a Hilbert–Smith theorem.
-/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Topology
namespace HSFormal
section NormalizedHaar
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
/-- Haar measure normalized on the whole compact group, rather than on an unspecified
positive compact neighborhood. -/
def normalizedCompactHaar : Measure G :=
  Measure.haarMeasure (⊤ : PositiveCompacts G)
instance normalizedCompactHaar_isHaar : IsHaarMeasure (normalizedCompactHaar G) := by
  unfold normalizedCompactHaar
  infer_instance
instance normalizedCompactHaar_isProbability : IsProbabilityMeasure (normalizedCompactHaar G) := by
  constructor
  simpa only [normalizedCompactHaar, PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))
end NormalizedHaar
section Average
variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
end Average
section OrbitExtension
variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [CompactSpace G] [MetricSpace X] [ContinuousSMul G X]
end OrbitExtension
section PointDetector
variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
end PointDetector
end HSFormal
