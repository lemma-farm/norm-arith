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
/-- The terminal coordinate of a finite trajectory prefix. -/
theorem lastIndex_mem (n : ℕ) : n ∈ Finset.Iic n := Finset.mem_Iic.mpr le_rfl
/-- Shared measurability witness for both marked path constructions. -/
theorem lastState_measurable (S : Type*) [MeasurableSpace S] (n : ℕ) :
    Measurable (fun h : Finset.Iic n → S × ℝ => (h ⟨n, lastIndex_mem n⟩).1) :=
  measurable_fst.comp (measurable_pi_apply _)
/-- A finite-branching substochastic transition operator. -/
structure Transfer (S : Type*) where
  arity : S → ℕ
  weight : (x : S) → Fin (arity x) → ℝ
  next : (x : S) → Fin (arity x) → S
  weight_nonneg : ∀ x i, 0 ≤ weight x i
  row_le_one : ∀ x, ∑ i, weight x i ≤ 1
namespace Transfer
variable (T : Transfer S)
def apply (f : S → ℝ) (x : S) : ℝ := ∑ i, T.weight x i * f (T.next x i)
end Transfer
/-- Literal finite channel rates; channels may share a successor. -/
structure FiniteRateModel (S : Type*) where
  arity : S → ℕ
  rate : (x : S) → Fin (arity x) → ℝ
  next : (x : S) → Fin (arity x) → S
  rate_nonneg : ∀ x i, 0 ≤ rate x i
  total_pos : ∀ x, 0 < ∑ i, rate x i
namespace FiniteRateModel
variable (M : FiniteRateModel S)
def total (x : S) : ℝ := ∑ i, M.rate x i
theorem total_positive (x : S) : 0 < M.total x := M.total_pos x
def jumpWeight (x : S) (i : Fin (M.arity x)) : ℝ := M.rate x i / M.total x
theorem jumpWeight_nonneg (x : S) (i : Fin (M.arity x)) : 0 ≤ M.jumpWeight x i :=
  div_nonneg (M.rate_nonneg x i) (M.total_positive x).le
theorem jumpWeight_sum (x : S) : ∑ i, M.jumpWeight x i = 1 := by
  simp only [jumpWeight, ← Finset.sum_div]
  change M.total x / M.total x = 1
  exact div_self (M.total_positive x).ne'
noncomputable def jumpPMF (x : S) : PMF (Fin (M.arity x)) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (M.jumpWeight x i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => M.jumpWeight_nonneg x i), M.jumpWeight_sum]
    simp)
section PathLaw
open MeasureTheory ProbabilityTheory Preorder
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
def jumpStatePMF (x : S) : PMF S := (M.jumpPMF x).map (M.next x)
/-- The next count state and the holding time are conditionally independent.
The holding is stored with its destination, so coordinate `n+1` contains the
duration spent at the state in coordinate `n`. -/
def markedStepLaw (x : S) : Measure (S × ℝ) :=
  (M.jumpStatePMF x).toMeasure.prod (expMeasure (M.total x))
instance markedStepLaw_probability (x : S) : IsProbabilityMeasure (M.markedStepLaw x) := by
  have : IsProbabilityMeasure (expMeasure (M.total x)) :=
    isProbabilityMeasure_expMeasure (M.total_positive x)
  unfold markedStepLaw
  infer_instance
def markedKernel : Kernel S (S × ℝ) where
  toFun := M.markedStepLaw
  measurable' := measurable_of_countable _
instance markedKernel_markov : IsMarkovKernel M.markedKernel where
  isProbabilityMeasure x := M.markedStepLaw_probability x
def pathKernel (n : ℕ) : Kernel (Finset.Iic n → S × ℝ) (S × ℝ) :=
  M.markedKernel.comap (fun h => (h ⟨n, lastIndex_mem n⟩).1) (lastState_measurable S n)
instance pathKernel_markov (n : ℕ) : IsMarkovKernel (M.pathKernel n) := by
  unfold pathKernel
  infer_instance
/-- An actual probability measure on infinite state/holding trajectories,
constructed by Ionescu--Tulcea from the literal rates and exponential law. -/
def pathLaw (x : S) : Measure (ℕ → S × ℝ) :=
  Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x, (0 : ℝ)))
instance pathLaw_probability (x : S) : IsProbabilityMeasure (M.pathLaw x) := by
  unfold pathLaw
  infer_instance
end PathLaw
end FiniteRateModel
open MeasureTheory ProbabilityTheory Set
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace Transfer
variable (T : Transfer S)
end Transfer
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
end
end DividingCompartments.FiniteBranching
