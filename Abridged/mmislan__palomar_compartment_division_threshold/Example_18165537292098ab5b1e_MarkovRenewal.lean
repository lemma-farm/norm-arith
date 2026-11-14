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

-- ==== Examples.mmislan__palomar_compartment_division_threshold.Dependencies.v27cdbf48217a.proofs.DividingCompartments.FiniteBranching ====
public section
set_option warningAsError true
@[expose] public section
/-!
State-dependent finite-row Markov-renewal foundation. Adapted from the existing
PositiveRecurrence.JumpChainFoster source SHA256 74a6c572d2ed0c4d30a9e5b28a95fa74473e2642b52ca97a3588474755231e1e.
Every row uses Fin(arity x); there is no uniform action-count bound. The source
generator adapter is a separate obligation. All path and clock theorems below
must pass strict compilation before being used.
-/
namespace DividingCompartments.FiniteBranching
open scoped BigOperators ENNReal
open Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S : Type*}
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.FiniteBranching.lastIndex_mem : ∀ (n : ℕ), n ∈ Finset.Iic n
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.FiniteBranching.lastState_measurable.{w_u_2} : ∀ (S : Type w_u_2) [inst : MeasurableSpace S] (n : ℕ),
  Measurable fun (h : ↥(Finset.Iic n) → S × ℝ) ↦
    (h ⟨n, DividingCompartments.FiniteBranching.lastIndex_mem n⟩).1

namespace Transfer


end Transfer

namespace FiniteRateModel


section PathLaw
open MeasureTheory ProbabilityTheory Preorder
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

end PathLaw
end FiniteRateModel
open MeasureTheory ProbabilityTheory Set

namespace FiniteRateModel
open Preorder

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel
open Preorder

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace Transfer


end Transfer

namespace FiniteRateModel
open Preorder

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

end FiniteRateModel
end
end DividingCompartments.FiniteBranching

end
end

-- ==== Examples.mmislan__palomar_compartment_division_threshold.Examples.Example_18165537292098ab5b1e_MarkovRenewal ====
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
axiom _root_.DividingCompartments.MarkovRenewal.Model.rate_pos.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  (x : S), 0 < M.rate x
def apply (f : S → ℝ) (x : S) : ℝ := ∫ y, f y ∂M.step x
def iter (M : Model S) : ℕ → (S → ℝ) → S → ℝ
  | 0,f => f
  | n+1,f => M.apply (M.iter n f)

variable [Countable S] [MeasurableSingletonClass S]

set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.reward_series_bound.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  [Countable S] [MeasurableSingletonClass S] {V c : S → ℝ},
  DividingCompartments.MarkovRenewal.Bounded V →
    DividingCompartments.MarkovRenewal.Bounded c →
      (∀ (x : S), 0 ≤ V x) →
        (∀ (x : S), 0 ≤ c x) →
          (∀ (x : S), M.apply V x + c x ≤ V x) →
            ∀ (x : S), (Summable fun (n : ℕ) ↦ M.iter n c x) ∧ ∑' (n : ℕ), M.iter n c x ≤ V x
def markedStepLaw (x : S) : Measure (S × ℝ) := (M.step x).prod (expMeasure (M.rate x))

def markedKernel : Kernel S (S × ℝ) where
  toFun := M.markedStepLaw
  measurable' := measurable_of_countable _

def pathKernel (n : ℕ) : Kernel (Finset.Iic n → S × ℝ) (S × ℝ) :=
  M.markedKernel.comap (fun h => (h ⟨n, FiniteBranching.lastIndex_mem n⟩).1)
    (FiniteBranching.lastState_measurable S n)
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.pathMarkov.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  [inst_1 : Countable S] [inst_2 : MeasurableSingletonClass S] (n : ℕ),
  ProbabilityTheory.IsMarkovKernel (M.pathKernel n)
attribute [instance] _root_.DividingCompartments.MarkovRenewal.Model.pathMarkov
def pathLaw (x : S) : Measure (ℕ → S × ℝ) :=
  Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x,(0 : ℝ)))

omit [Countable S] [MeasurableSingletonClass S] in
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.bounded_div_rate.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  {f : S → ℝ},
  DividingCompartments.MarkovRenewal.Bounded f →
    DividingCompartments.MarkovRenewal.Bounded fun (x : S) ↦ f x / M.rate x

def occupation (f : S → ℝ) (w : ℕ → S × ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (f (w n).1)*ENNReal.ofReal (max 0 (w (n+1)).2)
set_option linter.unusedVariables false in
axiom _root_.DividingCompartments.MarkovRenewal.Model.occupation_expectation.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (M : DividingCompartments.MarkovRenewal.Model S)
  [inst_1 : Countable S] [inst_2 : MeasurableSingletonClass S] {f : S → ℝ},
  DividingCompartments.MarkovRenewal.Bounded f →
    (∀ (x : S), 0 ≤ f x) →
      ∀ (x : S),
        (Summable fun (n : ℕ) ↦ M.iter n (fun (y : S) ↦ f y / M.rate y) x) →
          ∫⁻ (w : ℕ → S × ℝ), DividingCompartments.MarkovRenewal.Model.occupation f w ∂M.pathLaw x =
            ENNReal.ofReal (∑' (n : ℕ), M.iter n (fun (y : S) ↦ f y / M.rate y) x)
theorem occupation_budget {V : S → ℝ} (hV : Bounded V) (hV0 : ∀ x, 0 ≤ V x)
    {k : ℝ} (hk : 0 < k) (hstep : ∀ x, M.apply V x+k*(V x/M.rate x) ≤ V x)
    (x : S) : (∫⁻ w, occupation V w ∂M.pathLaw x) ≤ ENNReal.ofReal (V x/k) := by
  have hU : Bounded (fun y => V y/k) := by
    obtain ⟨C,hC,hV⟩ := hV
    refine ⟨C/k,div_nonneg hC hk.le,fun y => ?_⟩
    rw [abs_div,abs_of_pos hk]
    exact div_le_div_of_nonneg_right (hV y) hk.le
  have hU0 : ∀ y, 0 ≤ V y/k := fun y => div_nonneg (hV0 y) hk.le
  have hc := M.bounded_div_rate hV
  have hc0 : ∀ y, 0 ≤ V y/M.rate y := fun y => div_nonneg (hV0 y) (M.rate_pos y).le
  have hh : ∀ y, M.apply (fun z => V z/k) y+V y/M.rate y ≤ V y/k := by
    intro y
    have he : M.apply (fun z => V z/k) y=M.apply V y/k := integral_div k V
    rw [he]
    apply (le_div_iff₀ hk).mpr
    rw [add_mul,div_mul_cancel₀ _ hk.ne']
    nlinarith [hstep y]
  obtain ⟨hs,hb⟩ := M.reward_series_bound hU hc hU0 hc0 hh x
  rw [M.occupation_expectation hV hV0 x hs]
  exact ENNReal.ofReal_le_ofReal hb
end Model
end
end DividingCompartments.MarkovRenewal
