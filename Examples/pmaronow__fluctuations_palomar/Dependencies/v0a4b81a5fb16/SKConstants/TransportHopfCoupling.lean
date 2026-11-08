module
public import Mathlib
/-!
Adapted from OpenAI/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Original source: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI
License: Apache-2.0. Namespaces and module exports were adapted for the
pinned SK development; the analytic proofs are retained.
-/
@[expose] public section
/- Original module: Geometry/WeakHessian/Transport/CompactBounded.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
namespace WeakHessianTransport
variable {Z : Type*} [MetricSpace Z]
variable [ProperSpace Z]
variable [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]
end WeakHessianTransport
end
end SKConstants
/- Original module: Geometry/WeakHessian/Transport/UpperEnvelope.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
namespace WeakHessianTransport
variable {A E : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup E] [Module ℝ E]
variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]
variable (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (l : E →ₗ[ℝ] ℝ)
  (hl : Monotone l) (hcomp : ∀ a, l (T a) = c a)
  (hmajor : ∀ x : E, ∃ a : A, x ≤ T a)
end WeakHessianTransport
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
end
end InlinedFile0
end SKConstants
/- Original module: Geometry/WeakHessian/Transport/BoundedMarginalSum.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
variable [ProperSpace X] [ProperSpace Y]
end WeakHessianTransport
end
end InlinedFile0
end SKConstants
/- Original module: Geometry/WeakHessian/Transport/HopfObjective.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]
end WeakHessianTransport
end
end InlinedFile0
end SKConstants
/- Original module: Geometry/WeakHessian/Transport/TruncatedQuadraticCost.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
namespace WeakHessianTransport
open Set MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
local instance boundedPosSMulMono : PosSMulMono ℝ ((X×Y) →ᵇ ℝ) where
  smul_le_smul_of_nonneg_left scalar nonneg left right pointwise := fun point =>
    mul_le_mul_of_nonneg_left (a := scalar) (b := left point) (c := right point)
      (pointwise point) nonneg
end WeakHessianTransport
namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X]
end WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction
end
end InlinedFile0
end SKConstants
/- Original module: Geometry/WeakHessian/Transport/ProbabilityTightMarginals.lean -/
namespace SKConstants
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
end WeakHessianTransport
namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
end WeakHessianTransport
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
end
end InlinedFile0
end SKConstants
