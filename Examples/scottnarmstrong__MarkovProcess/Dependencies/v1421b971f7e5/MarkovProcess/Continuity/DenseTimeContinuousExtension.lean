/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.Basic
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Time.CountableDenseTime
import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/
open MeasureTheory Set
namespace MarkovProcess
noncomputable section
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
/-- Restriction of a continuous path to the fixed dense time carrier. -/
def denseRestriction (omega : ContinuousPath alpha) : DenseTime → alpha :=
  fun q ↦ omega (DenseTime.castOrderEmbedding q)
theorem denseRange_castOrderEmbedding : DenseRange DenseTime.castOrderEmbedding := by
  rw [DenseRange]
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  exact ⟨DenseTime.castOrderEmbedding q, ⟨q, rfl⟩, haq, hqb⟩
/-- A continuous path is determined by its values at the dense times. -/
theorem denseRestriction_injective [T2Space alpha] :
    Function.Injective (denseRestriction (alpha := alpha)) := by
  intro omega eta h
  apply ContinuousMap.ext
  have heq : (omega : NNReal → alpha) = eta :=
    denseRange_castOrderEmbedding.equalizer omega.continuous eta.continuous h
  exact congrFun heq
/-- A total extension, equal to the inverse on the restriction range and arbitrarily equal to
`default` away from that range. -/
def continuousExtension (default : ContinuousPath alpha) :
    (DenseTime → alpha) → ContinuousPath alpha :=
  Function.extend denseRestriction id (fun _ ↦ default)
section Measurable
variable [MeasurableSpace alpha] [BorelSpace alpha]
/-- Dense-time restriction is coordinatewise Borel measurable. -/
theorem measurable_denseRestriction : Measurable (denseRestriction (alpha := alpha)) := by
  rw [measurable_pi_iff]
  intro q
  exact
    (continuous_eval (alpha := alpha) (DenseTime.castOrderEmbedding q)).borel_measurable.mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
/-- Dense-time restriction is a measurable embedding. -/
theorem measurableEmbedding_denseRestriction :
    MeasurableEmbedding (denseRestriction (alpha := alpha)) :=
  measurable_denseRestriction.measurableEmbedding denseRestriction_injective
theorem measurable_continuousExtension (default : ContinuousPath alpha) :
    Measurable (continuousExtension (alpha := alpha) default) :=
  measurableEmbedding_denseRestriction.measurable_extend measurable_id measurable_const
end Measurable
end ContinuousPath
end
end MarkovProcess
