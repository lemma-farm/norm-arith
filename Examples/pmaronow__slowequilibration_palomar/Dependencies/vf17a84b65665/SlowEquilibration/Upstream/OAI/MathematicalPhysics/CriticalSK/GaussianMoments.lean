-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open scoped BigOperators InnerProductSpace
open Module
open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK
def standardGaussianProduct (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1
section
open Set Filter MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι]
def gaussianScalarPi (v : ℝ≥0) : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 v
instance (v : ℝ≥0) : IsProbabilityMeasure (gaussianScalarPi (ι := ι) v) := by unfold gaussianScalarPi; infer_instance
end
open Set Filter MeasureTheory ProbabilityTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end CriticalSK
end
end OAI
