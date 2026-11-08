/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Killed.Kernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# A positive exponential moment for the exit time

A uniform bound on the survival probability at one horizon `t0` propagates to the multiples of
that horizon by the Chapman--Kolmogorov law for the killed kernels: if the process started
anywhere survives the horizon `t0` inside the open set `U` with probability at most `q`, then it
survives `k` horizons with probability at most `q ^ k`
(`IsConservative.measure_lt_exitTime_nsmul_le`).  Summing the resulting geometric layers bounds a
*positive* exponential moment of the exit time
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le`), for every rate `lam` with
`q * exp (lam * t0) < 1`.

The positive exponential weight is `ContinuousPath.exponentialStoppingWeight`, which takes the
value `⊤` where the time is infinite.  That branch is forced: reading the extended time through
`ENNReal.toReal` would return `1` at `⊤` and silently discard the paths that never leave `U`.  A
finite integral of the weight therefore certifies almost-sure finiteness
(`ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top`), which the survival
bound supplies on its own
(`IsConservative.ae_exitTime_lt_top_of_measure_lt_exitTime_le`).

Two consequences are recorded.  An expected-exit-time bound `E_y τ_U ≤ M` valid from every
starting point supplies the survival hypothesis at the horizon `t0 = K M` with `q = K⁻¹` by
Markov's inequality, for every multiplier `K > 1`
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul`; the
multiplier `K = 2` is
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le`), and a large
multiplier normalizes the moment to `2` at a rate that is still positive
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le`).  The
elementary pointwise bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` converts an
exponential moment into every polynomial moment
(`IsConservative.lintegral_exitTime_pow_le`).

Every statement is an inequality of `ℝ≥0∞`-valued integrals; no integrability side condition and
no real-valued restatement appears.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
/-- The exponential weight at rate `lam` of an extended-real time functional, with the value `⊤`
on the infinite branch. -/
noncomputable def exponentialStoppingWeight (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  if sigma omega = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (lam * (sigma omega).toReal))
/-- On the finite branch the exponential weight is the ordinary exponential. -/
theorem exponentialStoppingWeight_of_ne_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega ≠ ⊤) :
    exponentialStoppingWeight lam sigma omega =
      ENNReal.ofReal (Real.exp (lam * (sigma omega).toReal)) :=
  if_neg h
/-- On the infinite branch the exponential weight is `⊤`. -/
theorem exponentialStoppingWeight_of_eq_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega = ⊤) :
    exponentialStoppingWeight lam sigma omega = ⊤ :=
  if_pos h
end ContinuousPath
namespace SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
/-- The elementary bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` on the nonnegative
half-line. -/
private theorem pow_le_mul_exp (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ p ≤ ((p : ℝ) / (lam * Real.exp 1)) ^ p * Real.exp (lam * t) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simpa only [pow_zero, one_mul] using Real.one_le_exp (mul_nonneg hlam.le ht)
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hst : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have h1 : lam * t / (p : ℝ) ≤ Real.exp (lam * t / (p : ℝ) - 1) := by
    have h := Real.add_one_le_exp (lam * t / (p : ℝ) - 1)
    linarith only [h]
  have h2 : (lam * t / (p : ℝ)) ^ p ≤ Real.exp (lam * t / (p : ℝ) - 1) ^ p :=
    pow_le_pow_left₀ (by positivity) h1 p
  have h3 : Real.exp (lam * t / (p : ℝ) - 1) ^ p = Real.exp (lam * t) / Real.exp 1 ^ p := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    field_simp
  rw [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ ((p : ℝ) / lam) ^ p)
  have h5 : ((p : ℝ) / lam) ^ p * (lam * t / (p : ℝ)) ^ p = t ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h6 : ((p : ℝ) / lam) ^ p * (Real.exp (lam * t) / Real.exp 1 ^ p) =
      ((p : ℝ) / (lam * Real.exp 1)) ^ p * Real.exp (lam * t) := by
    rw [div_pow, div_pow, mul_pow]
    field_simp
  rw [h5, h6] at h4
  exact h4
omit [LocallyCompactSpace alpha] in
/-- **Every polynomial moment from one exponential moment.**  For a positive rate the exit time
has all its moments controlled by the exponential moment, with the explicit constant
`(p / (lam * e)) ^ p`.  Taking `p = 2` bounds the second moment. -/
theorem IsConservative.lintegral_exitTime_pow_le
    (U : Set alpha) (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
        ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  have hconst : (0 : ℝ) < ((p : ℝ) / (lam * Real.exp 1)) ^ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp only [hp, pow_zero]
      norm_num
    · have : (0 : ℝ) < (p : ℝ) / (lam * Real.exp 1) := by
        have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
        positivity
      exact pow_pos this p
  have hpoint : ∀ omega : ContinuousPath alpha,
      ContinuousPath.exitTime U omega ^ p ≤
        ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
          ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega := by
    intro omega
    by_cases hne : ContinuousPath.exitTime U omega = ⊤
    · rw [ContinuousPath.exponentialStoppingWeight_of_eq_top lam _ hne,
        ENNReal.mul_top (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hconst)]
      exact le_top
    · rw [ContinuousPath.exponentialStoppingWeight_of_ne_top lam _ hne,
        ← ENNReal.ofReal_mul hconst.le]
      nth_rewrite 1 [← ENNReal.ofReal_toReal hne]
      rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_mul_exp lam hlam p _ ENNReal.toReal_nonneg)
  calc
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p ∂(IsConservative.continuousProcess P hP x)
        ≤ ∫⁻ omega, ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
            ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
          ∂(IsConservative.continuousProcess P hP x) := lintegral_mono hpoint
    _ = ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
          ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam
            (ContinuousPath.exitTime U) omega ∂(IsConservative.continuousProcess P hP x) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end
end SubMarkovKernelSemigroup
end MarkovProcess
