module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measure bookkeeping for the near-one density argument

This module proves the finite-support parabolic norm bound and the exact
strict-sublevel complement identity used by the near-one density-to-point
argument.  It has no coefficient, ABP, or density-to-point conclusion.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped ENNReal Topology
private theorem parabolicExponent_ne_zero (d : Nat) : parabolicExponent d ≠ 0 := by
  simp [parabolicExponent]
private theorem parabolicExponent_ne_top (d : Nat) : parabolicExponent d ≠ ∞ := by
  simp [parabolicExponent]
private theorem parabolicExponent_toReal (d : Nat) :
    (parabolicExponent d).toReal = (d : Real) + 1 := by
  unfold parabolicExponent
  have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
  rw [hcast, ENNReal.toReal_natCast]
  norm_num
theorem parabolicELpNormOn_le_of_norm_le_indicator
    (d : Nat) (f : TimeVelocity d → Real) (s E : Set (TimeVelocity d))
    (M : Real) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _ : TimeVelocity d ↦ M) z) :
    parabolicELpNormOn d f s ≤
      ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
  have hmono : eLpNorm f (parabolicExponent d) (volume.restrict s) ≤
      eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
        (parabolicExponent d) (volume.restrict s) :=
    eLpNorm_mono_ae hf (ae_restrict_of_forall_mem hs (by
      intro z hz
      by_cases hzE : z ∈ E
      · simpa only [Set.indicator_of_mem hzE, Real.norm_eq_abs, abs_of_nonneg hM]
          using hbound z hz
      · simpa only [Set.indicator_of_notMem hzE, norm_zero] using hbound z hz))
  calc
    parabolicELpNormOn d f s = eLpNorm f (parabolicExponent d) (volume.restrict s) := rfl
    _ ≤ eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
        (parabolicExponent d) (volume.restrict s) := hmono
    _ = ‖M‖ₑ * (volume.restrict s E) ^ (1 / (parabolicExponent d).toReal) :=
      eLpNorm_indicator_const hE.nullMeasurableSet (parabolicExponent_ne_zero d)
        (parabolicExponent_ne_top d)
    _ = ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
      rw [Measure.restrict_apply hE, inter_comm, parabolicExponent_toReal]
      rw [Real.enorm_of_nonneg hM]
end HypoellipticAleksandrov.Parabolic
