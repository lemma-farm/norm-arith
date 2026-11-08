/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Feller.Semigroup
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.C0SemigroupJoint
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/
open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty
namespace MarkovProcess
namespace Semigroup.StronglyContinuousContractionSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A strongly continuous contraction semigroup acts continuously when both time and the vector
vary.  Strong continuity alone only states this for a fixed vector; contractivity makes the
dependence on the vector uniform in time. -/
theorem tendsto_apply_of_tendsto
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htime : ∀ᶠ x in l, dist (S (t x) f₀) (S t₀ f₀) < ε / 2 :=
    ((S.continuous f₀).tendsto t₀ |>.comp ht) (Metric.ball_mem_nhds _ hhalf)
  filter_upwards [hf (ε / 2) hhalf, htime] with x hx htx
  calc
    dist (S (t x) (f x)) (S t₀ f₀)
        ≤ dist (S (t x) (f x)) (S (t x) f₀) +
            dist (S (t x) f₀) (S t₀ f₀) := dist_triangle _ _ _
    _ ≤ dist (f x) f₀ + dist (S (t x) f₀) (S t₀ f₀) :=
      by
        simpa only [add_comm] using
          add_le_add_right (S.dist_apply_le (t x) (f x) f₀)
            (dist (S (t x) f₀) (S t₀ f₀))
    _ < ε / 2 + ε / 2 := add_lt_add hx htx
    _ = ε := add_halves ε
/-- Joint continuity of the semigroup action in time and the evolving vector. -/
theorem continuous_apply
    (S : StronglyContinuousContractionSemigroup E) :
    Continuous fun tf : NNReal × E ↦ S tf.1 tf.2 := by
  rw [continuous_iff_continuousAt]
  intro tf
  exact S.tendsto_apply_of_tendsto continuousAt_fst continuousAt_snd
end Semigroup.StronglyContinuousContractionSemigroup
namespace SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
end SubMarkovKernelSemigroup
end MarkovProcess
