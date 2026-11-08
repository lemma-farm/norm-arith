module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Interval integrations of the angular density and flux identities -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
/-- The oriented first angular moment from the source. -/
def bellmanAngularFirstMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z * f z
/-- The oriented second angular moment from the source. -/
def bellmanAngularSecondMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z ^ 2 * f z
theorem bellmanAngularMoment_intervalIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun z => z ^ n * f z) volume a b := by
  apply (intervalIntegrable_iff').mpr
  exact (hf.integrableOn_isCompact isCompact_uIcc).continuousOn_mul
    (by fun_prop) isCompact_uIcc
end HypoellipticAleksandrov.KineticAleksandrov
