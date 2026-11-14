module

public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.ProjIcc

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.FinChain ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite-state Markov chains in discrete time -/
@[expose] public section
namespace Rhone.MarkovChain
open Finset Matrix
structure FinChain (S : Type*) [Fintype S] where
  P : Matrix S S ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1
namespace FinChain
variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)
def expect (f : S → ℝ) : S → ℝ := C.P *ᵥ f

variable {C}
end FinChain
end Rhone.MarkovChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Process ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Discrete-time Markov processes and their trajectory laws -/
@[expose] public section
namespace Rhone.MarkovChain
open MeasureTheory ProbabilityTheory Finset Preorder
structure DiscreteProcess (S : Type*) [MeasurableSpace S] where
  step : Kernel S S
  [isMarkov : IsMarkovKernel step]
namespace DiscreteProcess
variable {S : Type*} [MeasurableSpace S] (P : DiscreteProcess S)

noncomputable def stepSeq (m : ℕ) : Kernel ((_ : Iic m) → S) S :=
  P.step.comap (fun x => x ⟨m, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)
set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.DiscreteProcess.instIsMarkovKernelForallSubtypeNatMemFinsetIicStepSeq.{w_u_1} : ∀ {S : Type w_u_1} [inst : MeasurableSpace S] (P : Rhone.MarkovChain.DiscreteProcess S) (m : ℕ),
  ProbabilityTheory.IsMarkovKernel (P.stepSeq m)
attribute [instance] _root_.Rhone.MarkovChain.DiscreteProcess.instIsMarkovKernelForallSubtypeNatMemFinsetIicStepSeq
noncomputable def traj : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) P.stepSeq 0).comap (fun x _ => x)
    (measurable_pi_iff.2 fun _ => measurable_id)

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

end DiscreteProcess
end Rhone.MarkovChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Trajectory ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
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
set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.sum_ofReal_P.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] (C : Rhone.MarkovChain.FinChain S) (x : S),
  ∑ y : S, ENNReal.ofReal (C.P x y) = 1
noncomputable def stepPMF (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (C.P x y)) (C.sum_ofReal_P x)
noncomputable def kernel : Kernel S S where
  toFun x := (C.stepPMF x).toMeasure
  measurable' := Measurable.of_discrete
set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.instIsMarkovKernelKernel.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : MeasurableSpace S]
  [inst_2 : DiscreteMeasurableSpace S] (C : Rhone.MarkovChain.FinChain S),
  ProbabilityTheory.IsMarkovKernel C.kernel
attribute [instance] _root_.Rhone.MarkovChain.FinChain.instIsMarkovKernelKernel

noncomputable def toProcess : DiscreteProcess S := ⟨C.kernel⟩
noncomputable def pathLaw (x : S) : Measure (ℕ → S) := C.toProcess.pathLaw x
set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.instIsProbabilityMeasureForallNatPathLaw.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : MeasurableSpace S]
  [inst_2 : DiscreteMeasurableSpace S] (C : Rhone.MarkovChain.FinChain S) (x : S),
  MeasureTheory.IsProbabilityMeasure (C.pathLaw x)
attribute [instance] _root_.Rhone.MarkovChain.FinChain.instIsProbabilityMeasureForallNatPathLaw
omit [DecidableEq S] in
set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.integrable_eval.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : MeasurableSpace S]
  [inst_2 : DiscreteMeasurableSpace S] (C : Rhone.MarkovChain.FinChain S) (f : S → ℝ) (n : ℕ)
  (x : S), MeasureTheory.Integrable (fun (ω : ℕ → S) ↦ f (ω n)) (C.pathLaw x)
end Rhone.MarkovChain.FinChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.ChainIncrements ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Increments of a harmonic function along a finite chain -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

set_option linter.unusedVariables false in
axiom _root_.Rhone.MarkovChain.FinChain.integral_mul_eval_succ_two.{w_u_1} : ∀ {S : Type w_u_1} [inst : Fintype S] [inst_1 : MeasurableSpace S]
  [inst_2 : DiscreteMeasurableSpace S] (C : Rhone.MarkovChain.FinChain S) (x : S) (n : ℕ)
  (G : S → S → ℝ) {h : (ℕ → S) → ℝ},
  MeasureTheory.StronglyMeasurable h →
    ∀ {B : ℝ},
      (∀ (ω : ℕ → S), |h ω| ≤ B) →
        ∫ (ω : ℕ → S), h ω * G (ω n) (ω (n + 1)) ∂C.pathLaw x =
          ∫ (ω : ℕ → S), h ω * C.expect (G (ω n)) (ω n) ∂C.pathLaw x
end Rhone.MarkovChain.FinChain

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_eee80daf73c776f2c82c_ChainPathMeasurable ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Measurability of rescaled chain paths and the fourth moment of one step -/
@[expose] public section
namespace Rhone
open MeasureTheory Filter Set  MarkovChain 
open scoped NNReal
variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
namespace MarkovChain.FinChain
variable [Fintype S] (C : FinChain S)
theorem integral_step_pow_four_le (g : S → ℝ) {q : ℝ}
    (hq : ∀ z, C.expect (fun w => (g w - g z) ^ 4) z ≤ q) (x : S) (l : ℕ) :
    ∫ ω, (g (ω (l + 1)) - g (ω l)) ^ 4 ∂C.pathLaw x ≤ q := by
  have h1 := C.integral_mul_eval_succ_two x l (fun a b => (g b - g a) ^ 4)
    (h := fun _ => (1 : ℝ)) stronglyMeasurable_const (B := 1) (fun _ => by simp)
  simp only [one_mul] at h1
  rw [h1]
  have hi : Integrable (fun ω : ℕ → S => C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l))
      (C.pathLaw x) := C.integrable_eval (fun z => C.expect (fun w => (g w - g z) ^ 4) z) l x
  calc ∫ ω, C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l) ∂C.pathLaw x
      ≤ ∫ _ω, q ∂C.pathLaw x := integral_mono hi (integrable_const q) fun ω => hq (ω l)
    _ = q := by simp
end MarkovChain.FinChain
end Rhone
