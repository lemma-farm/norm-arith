module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

-- ==== Examples.mmislan__palomar_compartment_division_threshold.Examples.Example_9e503db44f70dd588a84_MarkovRenewal ====
set_option warningAsError true
@[expose] public section
set_option backward.isDefEq.respectTransparency false
/-! Actual countable-state marked laws with arbitrary probability rows.
Bounded rewards permit arbitrary immigrant laws, including infinite moments.
No recurrence or occupation conclusion is a model field. -/
namespace DividingCompartments.MarkovRenewal
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
noncomputable section
def Bounded {S : Type*} (f : S → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C
structure Model (S : Type*) [MeasurableSpace S] where
  step : S → Measure S
  probability : ∀ x, IsProbabilityMeasure (step x)
  rate : S → ℝ
  rate_lower : ∀ x, 1 ≤ rate x
namespace Model
variable {S : Type*} [MeasurableSpace S] (M : Model S)
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.stepProbability.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  (x : S), MeasureTheory.IsProbabilityMeasure (M.step x)
attribute [instance] _root_.DividingCompartments.MarkovRenewal.Model.stepProbability

def apply (f : S → ℝ) (x : S) : ℝ := ∫ y, f y ∂M.step x
variable [Countable S] [MeasurableSingletonClass S]
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.bounded_integrable.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  [Countable S] [MeasurableSingletonClass S] {f : S → ℝ},
  DividingCompartments.MarkovRenewal.Bounded f → ∀ (x : S), MeasureTheory.Integrable f (M.step x)
theorem apply_bounded {f : S → ℝ} (hf : Bounded f) : Bounded (M.apply f) := by
  obtain ⟨C,hC,hf⟩ := hf
  have hi (x : S) := M.bounded_integrable ⟨C,hC,hf⟩ x
  refine ⟨C,hC,fun x => abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := integral_mono (integrable_const (-C)) (hi x) (fun y => (abs_le.mp (hf y)).1)
    simpa [apply] using hh
  · have hh := integral_mono (hi x) (integrable_const C) (fun y => (abs_le.mp (hf y)).2)
    simpa [apply] using hh
end Model
end
end DividingCompartments.MarkovRenewal
