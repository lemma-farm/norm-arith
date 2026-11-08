-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.BlockEnergy
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK
section
variable {Ω : Type*} [MeasurableSpace Ω]
end
abbrev TriSample (n : ℕ) := (ℕ → ℝ) × ChiRows n
def triLaw (n : ℕ) : Measure (TriSample n) := (diagonalLaw n).prod (chiRowLaw n)
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance
end CriticalSK
end
end OAI
