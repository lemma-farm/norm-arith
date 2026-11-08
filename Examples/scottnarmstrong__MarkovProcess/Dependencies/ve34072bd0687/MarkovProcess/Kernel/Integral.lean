/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.ve34072bd0687.MarkovProcess.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integration against a kernel

This file defines the raw real-valued integral operator associated with a
kernel.  Subinvariance of a measure makes this operator independent, almost
everywhere, of the chosen representative of its input.
-/
open MeasureTheory
open ProbabilityTheory
namespace MarkovProcess
variable {α : Type*} [MeasurableSpace α]
/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, f y ∂κ x
/-- Under subinvariance, integrating an almost-everywhere strongly measurable
function against `κ x` gives an almost-everywhere strongly measurable function
of `x`. -/
theorem AEStronglyMeasurable.kernelIntegral {μ : Measure α} {κ : Kernel α α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (hκμ : κ ∘ₘ μ ≤ μ) :
    AEStronglyMeasurable (kernelIntegral κ f) μ := by
  let hfComp : AEStronglyMeasurable f (κ ∘ₘ μ) :=
    hf.mono_ac (Measure.absolutelyContinuous_of_le hκμ)
  refine ⟨fun x ↦ MarkovProcess.kernelIntegral κ (hfComp.mk f) x, ?_, ?_⟩
  · exact hfComp.stronglyMeasurable_mk.integral_kernel
  · filter_upwards [Measure.ae_ae_of_ae_comp hfComp.ae_eq_mk] with x hx
    exact integral_congr_ae hx
end MarkovProcess
