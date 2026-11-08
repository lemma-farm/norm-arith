/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Mathlib.Probability.Independence.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite-product sampling and range-two Hoeffding bounds for observable scores -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Rhone.Statistics.Identifiability
namespace FinitePanelSampling
variable {Ω : Type*} [MeasurableSpace Ω]
def iidLaw (ν : Measure Ω) (S : ℕ) : Measure (Fin S → Ω) :=
  Measure.pi (fun _ => ν)
instance iidLaw_probability (ν : Measure Ω) [IsProbabilityMeasure ν] (S : ℕ) :
    IsProbabilityMeasure (iidLaw ν S) := by unfold iidLaw; infer_instance
def sampleMean {S : ℕ} (f : Ω → ℝ) (x : Fin S → Ω) : ℝ :=
  (∑ s : Fin S, f (x s)) / S
end FinitePanelSampling
end Rhone.Statistics.Identifiability
