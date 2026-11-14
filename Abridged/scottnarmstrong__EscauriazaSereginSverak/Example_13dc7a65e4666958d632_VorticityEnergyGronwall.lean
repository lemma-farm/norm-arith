module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- ==== Examples.scottnarmstrong__EscauriazaSereginSverak.Examples.Example_13dc7a65e4666958d632_VorticityEnergyGronwall ====
-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Scalar Grönwall estimate for vorticity energy

This scalar estimate is the time integration step in the smooth energy argument
for `lem:localized-vorticity-energy`.
-/
@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped Interval
namespace ESS

set_option linter.unusedVariables false in
/-- The scalar differential energy inequality controls both the supremum of
the energy and the time integral of a nonnegative dissipation term. -/
theorem vorticityEnergyGronwallDissipation {a b K e₀ : ℝ}
    {e de d f : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hecont : ContinuousOn e (Icc a b))
    (hdecont : Continuous de) (hdcont : Continuous d) (hfcont : Continuous f)
    (hepos : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hederiv : ∀ t ∈ Ico a b, HasDerivAt e (de t) t)
    (hineq : ∀ t ∈ Icc a b, de t + d t ≤ K * e t + f t)
    (hinit : e a ≤ e₀) 
    (h_ESS_vorticityEnergyGronwallCore : ∀ {a b K e₀ : ℝ} {e de f : ℝ → ℝ},
      a ≤ b →
        0 ≤ K →
          ContinuousOn e (Set.Icc a b) →
            Continuous f →
              (∀ t ∈ Set.Icc a b, 0 ≤ e t) →
                (∀ t ∈ Set.Icc a b, 0 ≤ f t) →
                  (∀ t ∈ Set.Ico a b, HasDerivAt e (de t) t) →
                    (∀ t ∈ Set.Ico a b, de t ≤ K * e t + f t) →
                      e a ≤ e₀ →
                        ∀ t ∈ Set.Icc a b, e t ≤ Real.exp (K * (b - a)) * (e₀ + ∫ (s : ℝ) in a..b, f s))
    :
    (∀ t ∈ Icc a b,
      e t ≤ Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) ∧
    (∫ t in a..b, d t ≤
      e₀ + K * (b - a) *
        (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
          (∫ s in a..b, f s)) := by
  have hdeineq : ∀ t ∈ Ico a b, de t ≤ K * e t + f t := by
    intro t ht
    have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have h := hineq t htcc
    have hd := hdpos t htcc
    linarith only [h, hd]
  have henergy := h_ESS_vorticityEnergyGronwallCore hab hK hecont hfcont hepos hfpos
    hederiv hdeineq hinit
  have hdeint : IntervalIntegrable de volume a b := hdecont.intervalIntegrable a b
  have hdint : IntervalIntegrable d volume a b := hdcont.intervalIntegrable a b
  have hfint : IntervalIntegrable f volume a b := hfcont.intervalIntegrable a b
  have heint : IntervalIntegrable e volume a b := by
    exact hecont.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, de t) = e b - e a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hecont
      (fun t ht => hederiv t ⟨le_of_lt ht.1, ht.2⟩) hdeint
  have hpoint : ∀ t ∈ Icc a b, d t + de t ≤ K * e t + f t := by
    intro t ht
    simpa [add_comm] using hineq t ht
  have hrightCont : ContinuousOn (fun t => K * e t + f t) (Icc a b) := by
    exact (continuousOn_const.mul hecont).add hfcont.continuousOn
  have hrightInt : IntervalIntegrable (fun t => K * e t + f t) volume a b :=
    hrightCont.intervalIntegrable_of_Icc hab
  have hKint : (∫ t in a..b, K * e t) = K * ∫ t in a..b, e t := by
    exact intervalIntegral.integral_const_mul K e
  have hint : (∫ t in a..b, d t) + (∫ t in a..b, de t) ≤
      K * (∫ t in a..b, e t) + (∫ t in a..b, f t) := by
    calc
      _ = ∫ t in a..b, (d t + de t) := by
        rw [intervalIntegral.integral_add hdint hdeint]
      _ ≤ ∫ t in a..b, (K * e t + f t) :=
        intervalIntegral.integral_mono_on hab
          ((hdcont.add hdecont).intervalIntegrable a b) hrightInt
          (fun t ht => by simpa [add_comm] using hpoint t ht)
      _ = K * (∫ t in a..b, e t) + (∫ t in a..b, f t) := by
        calc
          _ = (∫ t in a..b, K * e t) + (∫ t in a..b, f t) :=
            intervalIntegral.integral_add (heint.const_mul K) hfint
          _ = K * (∫ t in a..b, e t) + (∫ t in a..b, f t) :=
            congrArg (fun x => x + (∫ t in a..b, f t)) hKint
  have hIntE : ∫ t in a..b, e t ≤
      (b - a) * (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) := by
    calc
      _ ≤ ∫ t in a..b,
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) :=
        intervalIntegral.integral_mono_on hab heint
          (continuousOn_const.intervalIntegrable_of_Icc hab)
          (fun t ht => henergy t ht)
      _ = (b - a) * (Real.exp (K * (b - a)) *
          (e₀ + (∫ s in a..b, f s))) := by
        rw [intervalIntegral.integral_const]
        ring
  have hfinal : ∫ t in a..b, d t ≤
      e₀ + K * (b - a) *
        (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
          (∫ s in a..b, f s) := by
    rw [hFTC] at hint
    have hbnonneg : 0 ≤ e b := hepos b ⟨hab, le_rfl⟩
    have he0bound : e a ≤ e₀ := hinit
    have hKmul := mul_le_mul_of_nonneg_left hIntE hK
    have hKmul' : K * (∫ t in a..b, e t) ≤
        K * (b - a) * (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) := by
      calc
        _ ≤ K * ((b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s)))) := hKmul
        _ = _ := by ring
    have hstep₁ : ∫ t in a..b, d t ≤
        (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) + (e a - e b) := by
      linarith only [hint]
    have hstep₂ : (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) +
        (e a - e b) ≤
        e₀ + K * (b - a) *
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
            (∫ s in a..b, f s) := by
      calc
        _ = K * (∫ t in a..b, e t) + ((∫ s in a..b, f s) + (e a - e b)) := by ring_nf
        _ ≤ K * (b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
              ((∫ s in a..b, f s) + (e a - e b)) :=
          add_le_add_left hKmul' _
        _ = (K * (b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
              (∫ s in a..b, f s)) + (e a - e b) := by ring_nf
        _ ≤ _ := by linarith only [hbnonneg, he0bound]
    calc
      _ ≤ (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) + (e a - e b) := hstep₁
      _ ≤ e₀ + K * (b - a) *
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
            (∫ s in a..b, f s) := hstep₂
  exact ⟨henergy, hfinal⟩
end ESS
