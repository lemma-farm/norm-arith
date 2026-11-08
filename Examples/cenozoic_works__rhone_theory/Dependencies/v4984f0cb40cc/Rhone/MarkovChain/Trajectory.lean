/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Absorption
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Process
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # The trajectory law of a finite chain -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)
omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem sum_ofReal_P (x : S) : ∑ y, ENNReal.ofReal (C.P x y) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => C.nonneg x y, C.row_sum, ENNReal.ofReal_one]
noncomputable def stepPMF (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (C.P x y)) (C.sum_ofReal_P x)
noncomputable def kernel : Kernel S S where
  toFun x := (C.stepPMF x).toMeasure
  measurable' := Measurable.of_discrete
instance : IsMarkovKernel C.kernel :=
  ⟨fun x => by change IsProbabilityMeasure (C.stepPMF x).toMeasure; infer_instance⟩
omit [DecidableEq S] in
theorem kernel_apply_singleton (x y : S) : C.kernel x {y} = ENNReal.ofReal (C.P x y) := by
  change (C.stepPMF x).toMeasure {y} = _
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rfl
omit [DecidableEq S] in
theorem kernel_real_singleton (x y : S) : (C.kernel x).real {y} = C.P x y := by
  rw [measureReal_def, kernel_apply_singleton, ENNReal.toReal_ofReal (C.nonneg x y)]
omit [DecidableEq S] in
theorem integral_kernel (f : S → ℝ) (x : S) : ∫ y, f y ∂C.kernel x = C.expect f x := by
  rw [integral_fintype Integrable.of_finite, expect_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [kernel_real_singleton, smul_eq_mul]
noncomputable def toProcess : DiscreteProcess S := ⟨C.kernel⟩
noncomputable def pathLaw (x : S) : Measure (ℕ → S) := C.toProcess.pathLaw x
instance (x : S) : IsProbabilityMeasure (C.pathLaw x) := by
  rw [pathLaw]
  infer_instance
omit [DecidableEq S] in
theorem integrable_eval (f : S → ℝ) (n : ℕ) (x : S) :
    Integrable (fun ω : ℕ → S => f (ω n)) (C.pathLaw x) :=
  Integrable.of_bound
    ((Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)).aestronglyMeasurable
    (∑ z, |f z|) (Filter.Eventually.of_forall fun ω => (Real.norm_eq_abs _).le.trans
      (Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _) (mem_univ (ω n))))
end Rhone.MarkovChain.FinChain
