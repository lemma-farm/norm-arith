/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.ItoFormula
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.ItoMaximal
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.QuadraticVariationGrid
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.TightProduct
set_option autoImplicit false
@[expose] public section
/-!
# General Itô formula: exact partition reduction

This file records the algebraic reduction behind the time-dependent Itô
formula.  For a function `f(t, x)` and a process `X`, its increment along a
uniform partition is split exactly into

* the left time-derivative sum,
* the left space-derivative sum,
* the weighted quadratic-variation sum, and
* an explicit remainder.

Consequently, convergence in probability of the four analytic pieces implies
the almost-everywhere Itô identity.  The frozen-time and frozen-state Taylor
remainders with uniform bounds on compact rectangles, and the notion of a
continuous modification of a process together with its quadratic-variation
sums, complete the file; the continuous modification of a natural Itô
process is constructed in `ItoFormulaGeneral`.
-/
public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
noncomputable section
namespace StochasticCalculus
variable {W : Type*}  
  [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}
/-- The time partial derivative, with the state variable held fixed. -/
@[expose] noncomputable def itoTimeDerivative (f : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => f r x) s
/-- The space partial derivative, with the time variable held fixed. -/
@[expose] noncomputable def itoSpaceDerivative (f : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  deriv (f s) x
/-- The second space partial derivative. -/
@[expose] noncomputable def itoSpaceSecondDerivative (f : ℝ → ℝ → ℝ)
    (s x : ℝ) : ℝ :=
  deriv (deriv (f s)) x
/-- The left-endpoint time-derivative sum along the uniform `n`-partition. -/
@[expose] noncomputable def generalItoTimeApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoTimeDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      ((uniformPartitionTime t n (i + 1) : ℝ) -
        (uniformPartitionTime t n i : ℝ))
/-- The left-endpoint space-derivative sum against the increments of `X`. -/
@[expose] noncomputable def generalItoSpaceApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoSpaceDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega)
/-- The left-endpoint weighted quadratic-variation term, including the
coefficient `1 / 2`. -/
@[expose] noncomputable def generalItoQuadraticApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / 2 : ℝ) *
      itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega) ^ 2
/-- Fixed-time measurability of a process and continuity of the
second-derivative weight imply measurability of every weighted quadratic
partition sum. -/
theorem aestronglyMeasurable_generalItoQuadraticApprox
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoQuadraticApprox f X t n) P := by
  unfold generalItoQuadraticApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega) *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) ^ 2) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    have hpair : AEStronglyMeasurable
        (fun omega => ((uniformPartitionTime t n i : ℝ),
          X (uniformPartitionTime t n i) omega)) P :=
      aestronglyMeasurable_const.prodMk
        (hXmeas (uniformPartitionTime t n i))
    have hweight : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega)) P :=
      hsecond.comp_aestronglyMeasurable hpair
    have hincrement : AEStronglyMeasurable
        (fun omega => X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) P :=
      (hXmeas (uniformPartitionTime t n (i + 1))).sub
        (hXmeas (uniformPartitionTime t n i))
    exact (aestronglyMeasurable_const.mul hweight).mul (hincrement.pow 2)
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]
/-- The exact one-step residual after the time, space, and quadratic terms
have been removed from the increment of `f`. -/
@[expose] noncomputable def generalItoRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) : ℝ :=
  f s₁ x₁ - f s₀ x₀ -
    itoTimeDerivative f s₀ x₀ * (s₁ - s₀) -
    itoSpaceDerivative f s₀ x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s₀ x₀ * (x₁ - x₀) ^ 2
/-- Sum of the exact one-step residuals along the uniform `n`-partition. -/
@[expose] noncomputable def generalItoRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)
/-- Joint continuity of the function and its displayed partial derivatives,
together with fixed-time measurability of the process, makes every finite
general Taylor-remainder sum measurable. -/
theorem aestronglyMeasurable_generalItoRemainderApprox
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hdxx : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoRemainderApprox f X t n) P := by
  unfold generalItoRemainderApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        generalItoRemainderIncrement f
          (uniformPartitionTime t n i : ℝ)
          (uniformPartitionTime t n (i + 1) : ℝ)
          (X (uniformPartitionTime t n i) omega)
          (X (uniformPartitionTime t n (i + 1)) omega)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    let s₀ : ℝ := uniformPartitionTime t n i
    let s₁ : ℝ := uniformPartitionTime t n (i + 1)
    have hx₀ := hXmeas (uniformPartitionTime t n i)
    have hx₁ := hXmeas (uniformPartitionTime t n (i + 1))
    have hslice (F : ℝ × ℝ → ℝ) (hF : Continuous F) (s : ℝ) :
        Continuous (fun x => F (s, x)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have hv₀ : AEStronglyMeasurable (fun omega => f s₀ (X _ omega)) P :=
      (hslice _ hf s₀).comp_aestronglyMeasurable hx₀
    have hv₁ : AEStronglyMeasurable (fun omega => f s₁ (X _ omega)) P :=
      (hslice _ hf s₁).comp_aestronglyMeasurable hx₁
    have ht₀ : AEStronglyMeasurable
        (fun omega => itoTimeDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdt s₀).comp_aestronglyMeasurable hx₀
    have hx'₀ : AEStronglyMeasurable
        (fun omega => itoSpaceDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdx s₀).comp_aestronglyMeasurable hx₀
    have hxx₀ : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdxx s₀).comp_aestronglyMeasurable hx₀
    have hincrement := hx₁.sub hx₀
    unfold generalItoRemainderIncrement
    exact ((((hv₁.sub hv₀).sub
      (ht₀.mul aestronglyMeasurable_const)).sub
      (hx'₀.mul hincrement)).sub
      ((aestronglyMeasurable_const.mul hxx₀).mul (hincrement.pow 2)))
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]
/-- Time Taylor residual with the state frozen at the right endpoint of a
single process increment. -/
noncomputable def generalItoFrozenStateTimeRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₁ : ℝ) : ℝ :=
  f s₁ x₁ - f s₀ x₁ -
    itoTimeDerivative f s₀ x₁ * (s₁ - s₀)
/-- State Taylor residual with time frozen at the left endpoint of a single
process increment. -/
noncomputable def generalItoFrozenTimeStateRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ x₀ x₁ : ℝ) : ℝ :=
  f s₀ x₁ - f s₀ x₀ -
    itoSpaceDerivative f s₀ x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s₀ x₀ * (x₁ - x₀) ^ 2
omit   [MeasurableSpace W]  in
/-- The frozen-time state component is exactly the ordinary one-variable
second-order Taylor remainder of the corresponding time slice. -/
theorem generalItoFrozenTimeStateRemainderIncrement_eq_itoTaylorRemainder
    (f : ℝ → ℝ → ℝ) (s₀ x₀ x₁ : ℝ) :
    generalItoFrozenTimeStateRemainderIncrement f s₀ x₀ x₁ =
      itoTaylorRemainder (f s₀) x₀ x₁ := by
  unfold generalItoFrozenTimeStateRemainderIncrement itoTaylorRemainder
    itoSpaceDerivative itoSpaceSecondDerivative
  ring
/-- Mixed error caused by evaluating the time derivative at the left state
rather than the right state of a single process increment. -/
noncomputable def generalItoTimeStateCrossIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) : ℝ :=
  (itoTimeDerivative f s₀ x₁ - itoTimeDerivative f s₀ x₀) *
    (s₁ - s₀)
omit   [MeasurableSpace W]  in
/-- A frozen-state first-order time residual is controlled by the oscillation
of the time derivative on the corresponding time interval. -/
theorem abs_generalItoFrozenStateTimeRemainderIncrement_le
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₁ K : ℝ)
    (hfdiff : Differentiable ℝ (fun s => f s x₁))
    (hdt : Continuous (fun s => itoTimeDerivative f s x₁))
    (hbound : ∀ s ∈ Set.uIoc s₀ s₁,
      |itoTimeDerivative f s x₁ - itoTimeDerivative f s₀ x₁| ≤ K) :
    |generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁| ≤
      K * |s₁ - s₀| := by
  let F : ℝ → ℝ := fun s => f s x₁
  let D : ℝ → ℝ := fun s => itoTimeDerivative f s x₁
  have hDint : IntervalIntegrable D volume s₀ s₁ :=
    hdt.intervalIntegrable s₀ s₁
  have hconst : IntervalIntegrable (fun _ : ℝ => D s₀) volume s₀ s₁ :=
    intervalIntegrable_const
  have hfund : ∫ s in s₀..s₁, D s = F s₁ - F s₀ := by
    have hraw := intervalIntegral.integral_deriv_eq_sub
      (f := F) (fun s _hs => hfdiff.differentiableAt) (by
        simpa only [F, D, itoTimeDerivative] using hDint)
    simpa only [F, D, itoTimeDerivative] using hraw
  have heq : generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁ =
      ∫ s in s₀..s₁, D s - D s₀ := by
    rw [intervalIntegral.integral_sub hDint hconst, hfund,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    unfold generalItoFrozenStateTimeRemainderIncrement
    dsimp only [F, D]
    ring
  rw [heq]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => D s - D s₀) (C := K)
      (fun s hs => by
        simpa only [D, Real.norm_eq_abs] using hbound s hs))
omit   [MeasurableSpace W]  in
/-- Exact factorization of a genuinely two-variable one-step Itô residual.
It separates the two ordinary one-variable Taylor errors from the sole mixed
time/state cross term. -/
theorem generalItoRemainderIncrement_eq_frozenTime_frozenState_cross
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) :
    generalItoRemainderIncrement f s₀ s₁ x₀ x₁ =
      generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁ +
      generalItoFrozenTimeStateRemainderIncrement f s₀ x₀ x₁ +
      generalItoTimeStateCrossIncrement f s₀ s₁ x₀ x₁ := by
  unfold generalItoRemainderIncrement
    generalItoFrozenStateTimeRemainderIncrement
    generalItoFrozenTimeStateRemainderIncrement
    generalItoTimeStateCrossIncrement
  ring
/-- Accumulated frozen-state time Taylor residual along a uniform
partition. -/
noncomputable def generalItoFrozenStateTimeRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoFrozenStateTimeRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n (i + 1)) omega)
/-- Accumulated frozen-time state Taylor residual along a uniform
partition. -/
noncomputable def generalItoFrozenTimeStateRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoFrozenTimeStateRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)
/-- Accumulated mixed time/state cross error along a uniform partition. -/
noncomputable def generalItoTimeStateCrossApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoTimeStateCrossIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)
omit   [MeasurableSpace W]  in
/-- The full accumulated residual is exactly the sum of its frozen-state
time, frozen-time state, and mixed cross components. -/
theorem generalItoRemainderApprox_eq_frozenTime_frozenState_cross
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    generalItoRemainderApprox f X t n omega =
      generalItoFrozenStateTimeRemainderApprox f X t n omega +
      generalItoFrozenTimeStateRemainderApprox f X t n omega +
      generalItoTimeStateCrossApprox f X t n omega := by
  unfold generalItoRemainderApprox generalItoFrozenStateTimeRemainderApprox
    generalItoFrozenTimeStateRemainderApprox generalItoTimeStateCrossApprox
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact generalItoRemainderIncrement_eq_frozenTime_frozenState_cross
    f _ _ _ _
omit   [MeasurableSpace W]  in
/-- Subsequence form of the frozen-time state closure, used when quadratic
variation in probability supplies almost-sure convergence only after taking
a subsubsequence. -/
theorem generalItoFrozenTimeStateRemainderApprox_subseq_tendsto_zero_of_bound
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (k : ℕ → ℕ) (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (C : ℝ) (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (k n + 1) omega ≤ C)
    (hremainder : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ε * (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2) :
    Filter.Tendsto
      (fun n => generalItoFrozenTimeStateRemainderApprox
        f X t (k n + 1) omega) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨nq, hnq⟩ := Filter.eventually_atTop.1 hquadratic
  obtain ⟨nr, hnr⟩ :=
    Filter.eventually_atTop.1 (hk.eventually (hremainder δ hδ))
  refine ⟨max nq nr, fun n hn => ?_⟩
  have hq := hnq n ((le_max_left _ _).trans hn)
  have hr := hnr n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero]
  unfold generalItoFrozenTimeStateRemainderApprox
  calc
    |∑ i ∈ Finset.range (k n + 1),
        generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (k n + 1) i : ℝ)
          (X (uniformPartitionTime t (k n + 1) i) omega)
          (X (uniformPartitionTime t (k n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (k n + 1),
          |generalItoFrozenTimeStateRemainderIncrement f
            (uniformPartitionTime t (k n + 1) i : ℝ)
            (X (uniformPartitionTime t (k n + 1) i) omega)
            (X (uniformPartitionTime t (k n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k n + 1), δ *
        (X (uniformPartitionTime t (k n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (k n + 1) i) omega) ^ 2 :=
      Finset.sum_le_sum fun i hi => hr i hi
    _ = δ * quadraticVariationApprox X t (k n + 1) omega := by
      rw [← Finset.mul_sum]
      rfl
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hq hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [hC.ne']
    _ < ε := by linarith
omit   [MeasurableSpace W]  in
/-- Uniformly small oscillation of the time derivative within every fine
partition interval forces the accumulated frozen-state time Taylor error to
vanish. -/
theorem generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_derivative_oscillation
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hfdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1), ∀ s ∈ Set.uIoc
        (uniformPartitionTime t (n + 1) i : ℝ)
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ),
        |itoTimeDerivative f s
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤ δ)
    (hdt : ∀ x, Continuous (fun s => itoTimeDerivative f s x)) :
    Filter.Tendsto
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / ((t : ℝ) + 1)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε ht1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsmall δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  unfold generalItoFrozenStateTimeRemainderApprox
  calc
    |∑ i ∈ Finset.range (n + 1),
        generalItoFrozenStateTimeRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (n + 1),
          |generalItoFrozenStateTimeRemainderIncrement f
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
        ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime t (n + 1) i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        norm_cast
        unfold uniformPartitionTime
        gcongr
        omega
      simpa only [abs_of_nonneg (sub_nonneg.mpr htime)] using
        (abs_generalItoFrozenStateTimeRemainderIncrement_le
          f (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) δ
            (hfdiff _) (hdt _) (hN n hn i hi))
    _ = δ * (t : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ i ∈ Finset.range (n + 1),
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) =
            (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) 0 : ℝ) := by
          simpa using (Finset.sum_range_sub
            (fun i => (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1))
        _ = (t : ℝ) := by
          simp only [uniformPartitionTime, Nat.cast_add, Nat.cast_one,
            NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
          field_simp
          norm_num
    _ < ε := by
      calc
        δ * (t : ℝ) < δ * ((t : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (lt_add_one _) hδ
        _ = ε := by
          dsimp only [δ]
          exact div_mul_cancel₀ ε ht1.ne'
omit   [MeasurableSpace W]  in
/-- On a continuous compact path, joint continuity of the time derivative
makes its oscillation uniformly small within each sufficiently fine time
interval, even though the frozen state varies from interval to interval. -/
theorem generalItoTimeDerivative_time_oscillation_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1), ∀ s ∈ Set.uIoc
        (uniformPartitionTime t (n + 1) i : ℝ)
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ),
        |itoTimeDerivative f s
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤ δ := by
  let R : Set ℝ := (fun s : ℝ≥0 => X s omega) '' Set.Icc 0 t
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ R
  have hRcompact : IsCompact R := by
    simpa only [R] using isCompact_Icc.image_of_continuousOn hpath
  have hScompact : IsCompact S := isCompact_Icc.prod hRcompact
  have huc : UniformContinuousOn
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hdt.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  filter_upwards [continuousOn_uniformPartition_increments_tendsto
    (fun s : ℝ≥0 => (s : ℝ)) t NNReal.continuous_coe.continuousOn η hη]
    with n hn
  intro i hi s hs
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hile : i ≤ n + 1 := (Nat.le_add_right i 1).trans hipos
  have hti := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hti1 := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
      (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
    norm_cast
    unfold uniformPartitionTime
    gcongr
    omega
  rw [Set.uIoc_of_le htime] at hs
  let p : ℝ × ℝ :=
    (s, X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  let q : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  have hsIcc : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
    have hzero : (0 : ℝ) ≤ (uniformPartitionTime t (n + 1) i : ℝ) := by
      exact_mod_cast hti.1
    have htop : (uniformPartitionTime t (n + 1) (i + 1) : ℝ) ≤
        (t : ℝ) := by
      exact_mod_cast hti1.2
    constructor
    · exact hzero.trans hs.1.le
    · exact hs.2.trans htop
  have hxR : X (uniformPartitionTime t (n + 1) (i + 1)) omega ∈ R :=
    ⟨uniformPartitionTime t (n + 1) (i + 1), hti1, rfl⟩
  have hp : p ∈ S := ⟨hsIcc, hxR⟩
  have hq : q ∈ S := by
    refine ⟨⟨?_, ?_⟩, hxR⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
  have hpq : dist p q < η := by
    dsimp only [p, q]
    rw [dist_prod_same_right]
    have hle : dist s (uniformPartitionTime t (n + 1) i : ℝ) ≤
        dist (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (uniformPartitionTime t (n + 1) i : ℝ) := by
      rw [dist_comm s, dist_comm
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ)]
      have hsu : s ∈ Set.uIcc
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        rw [Set.uIcc_of_le htime]
        exact Set.Ioc_subset_Icc_self hs
      exact Real.dist_left_le_of_mem_uIcc
        hsu
    exact hle.trans_lt (by simpa only [Real.dist_eq] using hn i hi)
  have hout := hmod p hp q hq hpq
  dsimp only [p, q] at hout
  simpa only [Real.dist_eq] using hout.le
omit   [MeasurableSpace W]  in
/-- The frozen-state time component of the general Itô remainder vanishes
pathwise for a jointly continuous time derivative and time-differentiable
test function along every continuous sample path. -/
theorem generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hfdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0) := by
  apply generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_derivative_oscillation
    f X t omega hfdiff
      (generalItoTimeDerivative_time_oscillation_eventually_small
        f X t omega hdt hpath)
  intro x
  exact hdt.comp (continuous_id.prodMk continuous_const)
omit   [MeasurableSpace W]  in
/-- If the time derivative changes uniformly little across every state
increment of a fine partition, then the accumulated mixed time/state cross
term vanishes.  Continuity of the derivative along a continuous compact path
is intended to discharge the explicit `hsmall` premise. -/
theorem generalItoTimeStateCrossApprox_tendsto_zero_of_derivative_increments
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)| ≤ δ) :
    Filter.Tendsto
      (fun n => generalItoTimeStateCrossApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / ((t : ℝ) + 1)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε ht1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsmall δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  unfold generalItoTimeStateCrossApprox
  calc
    |∑ i ∈ Finset.range (n + 1),
        generalItoTimeStateCrossIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (n + 1),
          |generalItoTimeStateCrossIncrement f
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
        ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime t (n + 1) i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        norm_cast
        unfold uniformPartitionTime
        gcongr
        omega
      unfold generalItoTimeStateCrossIncrement
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr htime)]
      exact mul_le_mul_of_nonneg_right (hN n hn i hi) (sub_nonneg.mpr htime)
    _ = δ * (t : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      have hn0 : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
      calc
        (∑ i ∈ Finset.range (n + 1),
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) =
            (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) 0 : ℝ) :=
          by
            simpa using (Finset.sum_range_sub
              (fun i => (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1))
        _ = (t : ℝ) := by
          simp only [uniformPartitionTime, Nat.cast_add, Nat.cast_one,
            NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
          field_simp
          norm_num
    _ < ε := by
      calc
        δ * (t : ℝ) < δ * ((t : ℝ) + 1) := by
          exact mul_lt_mul_of_pos_left (lt_add_one _) hδ
        _ = ε := by
          dsimp only [δ]
          exact div_mul_cancel₀ ε ht1.ne'
omit   [MeasurableSpace W]  in
/-- Joint continuity of the time derivative and continuity of one sample path
make the derivative uniformly insensitive to adjacent state increments on a
fixed compact horizon. -/
theorem generalItoTimeDerivative_state_increments_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)| ≤ δ := by
  let R : Set ℝ := (fun s : ℝ≥0 => X s omega) '' Set.Icc 0 t
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ R
  have hRcompact : IsCompact R := by
    simpa only [R] using
      isCompact_Icc.image_of_continuousOn hpath
  have hScompact : IsCompact S := isCompact_Icc.prod hRcompact
  have huc : UniformContinuousOn
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hdt.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  filter_upwards [continuousOn_uniformPartition_increments_tendsto
    (fun s => X s omega) t hpath η hη] with n hn
  intro i hi
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hile : i ≤ n + 1 := (Nat.le_add_right i 1).trans hipos
  have hti := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hti1 := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  let p : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  let q : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) i) omega)
  have hp : p ∈ S := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
    · exact ⟨uniformPartitionTime t (n + 1) (i + 1), hti1, rfl⟩
  have hq : q ∈ S := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
    · exact ⟨uniformPartitionTime t (n + 1) i, hti, rfl⟩
  have hpq : dist p q < η := by
    dsimp only [p, q]
    rw [dist_prod_same_left, Real.dist_eq]
    exact hn i hi
  have hout := hmod p hp q hq hpq
  dsimp only [p, q] at hout
  simpa only [Real.dist_eq] using hout.le
omit   [MeasurableSpace W]  in
/-- The mixed time/state component of the general Itô remainder vanishes
pathwise along every continuous path when the time derivative is jointly
continuous. -/
theorem generalItoTimeStateCrossApprox_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => generalItoTimeStateCrossApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) :=
  generalItoTimeStateCrossApprox_tendsto_zero_of_derivative_increments
    f X t omega
      (generalItoTimeDerivative_state_increments_eventually_small
        f X t omega hdt hpath)
/-- A process `Y` is a continuous modification of `X` when the two agree
almost everywhere at each fixed time and `Y` has almost-everywhere continuous
sample paths.  The fixed-time quantifier is deliberately outside the
almost-everywhere quantifier, matching the standard notion of modification. -/
structure IsContinuousProcessModification
    (X Y : ℝ≥0 → W → ℝ) (P : Measure W) : Prop where
  fixedTime_ae_eq : ∀ s, X s =ᵐ[P] Y s
  continuous_paths : ∀ᵐ omega ∂P, Continuous (fun s => Y s omega)
/-- A fixed-time modification agrees simultaneously at every point of all
uniform partitions of a fixed horizon.  Countability of the two natural-number
indices is the key distinction from an uncountable simultaneous-time claim. -/
theorem fixedTime_ae_eq_uniformPartitions
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ n i : ℕ,
      X (uniformPartitionTime t (n + 1) i) omega =
        Y (uniformPartitionTime t (n + 1) i) omega := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro i
  exact hXY (uniformPartitionTime t (n + 1) i)
/-- For a process admitting a continuous modification, every deterministic
stopping boundary contributes vanishing quadratic mass in probability.  This
is the analytic boundary-error input for replacing stopped cumulative sums by
ordinary prefix sums in the weighted-bracket argument. -/
theorem IsContinuousProcessModification.quadraticVariationCrossingStopApprox_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t a : ℝ≥0) (ha : a ∈ Set.Icc 0 t) :
    TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X t (n + 1) a)
      Filter.atTop (fun _ => 0) := by
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hXmeas s).congr (hmod.fixedTime_ae_eq s)
  have hY : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox Y t (n + 1) a)
      Filter.atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_quadraticVariationCrossingStopApprox
        hYmeas t (n + 1) a
    · filter_upwards [hmod.continuous_paths] with omega hcontinuous
      exact quadraticVariationCrossingStopApprox_tendsto_zero_of_continuousOn
        Y t a omega ha hcontinuous.continuousOn
  exact hY.congr_left fun n =>
    (quadraticVariationCrossingStopApprox_ae_eq_of_fixedTime_ae_eq
      hmod.fixedTime_ae_eq t (n + 1) a).symm
/-- Once the stopped quadratic sums have a limit, continuity removes their
single partial boundary cell and gives the same limit for the completed cells
strictly before the stopping time. -/
theorem IsContinuousProcessModification.quadraticVariationBeforeStopApprox_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t a : ℝ≥0) (ha : a ∈ Set.Icc 0 t) (Q : W → ℝ)
    (hstop : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s => X (min s a)) t (n + 1))
      Filter.atTop Q) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox X t (n + 1) a)
      Filter.atTop Q := by
  have hcross :=
    hmod.quadraticVariationCrossingStopApprox_tendstoInMeasure
      hXmeas t a ha
  have hsub := hstop.sub_real_noMeas hcross
  have hsource : ∀ n,
      (fun omega =>
        quadraticVariationApprox (fun s => X (min s a)) t (n + 1) omega -
          quadraticVariationCrossingStopApprox X t (n + 1) a omega) =ᵐ[P]
        quadraticVariationBeforeStopApprox X t (n + 1) a := by
    intro n
    filter_upwards with omega
    rw [quadraticVariationApprox_stop_eq_before_add_crossing]
    ring
  simpa only [sub_zero] using hsub.congr_left hsource
/-- A continuous modification also supplies a sample-dependent compact-range
bound simultaneously on every uniform partition point of a fixed horizon.
This is the pathwise localization datum used to bound derivatives on compact
state ranges. -/
theorem IsContinuousProcessModification.uniformPartition_bounded
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, ∀ n i : ℕ, i ≤ n + 1 →
      |X (uniformPartitionTime t (n + 1) i) omega| ≤ K := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid] with omega hcontinuous hagree
  have hbounded : BddAbove
      ((fun s : ℝ≥0 => |Y s omega|) '' Set.Icc 0 t) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) t)).bddAbove_image
      hcontinuous.abs.continuousOn
  rcases hbounded with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro n i hi
  rw [hagree n i]
  apply hK
  exact ⟨uniformPartitionTime t (n + 1) i,
    uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) hi, rfl⟩
/-- A continuous modification localizes every continuous second-derivative
weight on the countable family of uniform grids.  The bound may depend on the
sample and horizon, but is simultaneous in the partition size and index. -/
theorem IsContinuousProcessModification.uniformPartition_secondDerivative_bounded
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧ ∀ n i : ℕ, i ≤ n + 1 →
      |itoSpaceSecondDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
        (X (uniformPartitionTime t (n + 1) i) omega)| ≤ K := by
  filter_upwards [hmod.uniformPartition_bounded t] with omega homega
  obtain ⟨R, hR⟩ := homega
  have hRnonneg : 0 ≤ R := by
    exact (abs_nonneg (X (uniformPartitionTime t 1 0) omega)).trans
      (hR 0 0 (by omega))
  let S : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.Icc (-R) R
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hbounded : BddAbove
      ((fun p : ℝ × ℝ => |itoSpaceSecondDerivative f p.1 p.2|) '' S) :=
    hcompact.bddAbove_image hsecond.abs.continuousOn
  obtain ⟨K, hK⟩ := hbounded
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n i hi
  apply (hK ?_).trans (le_max_left _ _)
  refine ⟨((uniformPartitionTime t (n + 1) i : ℝ),
    X (uniformPartitionTime t (n + 1) i) omega), ?_, rfl⟩
  have htime := uniformPartitionTime_mem_Icc_of_le
    t (Nat.zero_lt_succ n) hi
  have hstate := abs_le.mp (hR n i hi)
  exact ⟨⟨by exact_mod_cast htime.1, by exact_mod_cast htime.2⟩,
    hstate⟩
/-- Fixed-time modifications give the same time partition term almost
everywhere for every fixed finite partition. -/
theorem generalItoTimeApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoTimeApprox f X t n =ᵐ[P]
      generalItoTimeApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
        Y (uniformPartitionTime t n i) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      hXY (uniformPartitionTime t n i)
  filter_upwards [hall] with omega homega
  unfold generalItoTimeApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [homega i hi]
/-- Fixed-time modifications give the same explicit Taylor residual term
almost everywhere for every fixed finite partition. -/
theorem generalItoRemainderApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoRemainderApprox f X t n =ᵐ[P]
      generalItoRemainderApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold generalItoRemainderApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]
omit   [MeasurableSpace W]  in
/-- Exact four-term decomposition of a time-dependent function increment
along the uniform partition.  No differentiability or probability hypothesis
is needed: the remainder was defined to make this identity exact. -/
theorem generalIto_uniformPartition_decomposition
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    f t (X t omega) - f 0 (X 0 omega) =
      generalItoTimeApprox f X t (n + 1) omega +
      generalItoSpaceApprox f X t (n + 1) omega +
      generalItoQuadraticApprox f X t (n + 1) omega +
      generalItoRemainderApprox f X t (n + 1) omega := by
  have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  calc
    _ = f (uniformPartitionTime t (n + 1) (n + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) (n + 1)) omega) -
        f (uniformPartitionTime t (n + 1) 0 : ℝ)
          (X (uniformPartitionTime t (n + 1) 0) omega) := by
      simp only [htop, hzero, NNReal.coe_zero]
    _ = ∑ i ∈ Finset.range (n + 1),
        (f (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)) := by
      exact (Finset.sum_range_sub
        (fun i => f (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)) (n + 1)).symm
    _ = _ := by
      unfold generalItoTimeApprox generalItoSpaceApprox
        generalItoQuadraticApprox generalItoRemainderApprox
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      unfold generalItoRemainderIncrement
      ring
/-- The general Itô formula reduced to convergence in probability of its
partition terms.  This is the analytic interface needed by any future
continuous-modification and localization layer. -/
theorem generalIto_formula_ae_of_partition_limits
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        T omega + I omega + Q omega := by
  have htimeSpace := htime.add_real_noMeas hspace
  have hwithQuadratic := htimeSpace.add_real_noMeas hquadratic
  have htotal := hwithQuadratic.add_real_noMeas hremainder
  have htotal' : TendstoInMeasure P
      (fun n omega =>
        generalItoTimeApprox f X t (n + 1) omega +
          generalItoSpaceApprox f X t (n + 1) omega +
          generalItoQuadraticApprox f X t (n + 1) omega +
          generalItoRemainderApprox f X t (n + 1) omega)
      Filter.atTop (fun omega => T omega + I omega + Q omega) := by
    apply htotal.congr_right
    filter_upwards with omega
    simp only [add_zero]
  have hdecomp : ∀ n : ℕ,
      (fun omega =>
        generalItoTimeApprox f X t (n + 1) omega +
          generalItoSpaceApprox f X t (n + 1) omega +
          generalItoQuadraticApprox f X t (n + 1) omega +
          generalItoRemainderApprox f X t (n + 1) omega) =ᵐ[P]
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) := by
    intro n
    filter_upwards with omega
    exact (generalIto_uniformPartition_decomposition f X t n omega).symm
  have hconstantTarget : TendstoInMeasure P
      (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
      Filter.atTop (fun omega => T omega + I omega + Q omega) :=
    htotal'.congr_left hdecomp
  have hconstantSelf : TendstoInMeasure P
      (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
      Filter.atTop (fun omega => f t (X t omega) - f 0 (X 0 omega)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hendpoint) (by
      filter_upwards with omega
      exact tendsto_const_nhds)
  have hunique := tendstoInMeasure_ae_unique hconstantSelf hconstantTarget
  filter_upwards [hunique] with omega homega
  linarith
/-- Once the time, quadratic, and remainder sums have their intended limits,
the general Itô identity is equivalent to convergence of the concrete `dX`
left sums.  In particular, the stochastic term cannot be chosen independently
of the partition approximation. -/
theorem generalIto_formula_ae_iff_space_limit
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ↔
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          T omega + I omega + Q omega := by
  constructor
  · intro hspace
    exact generalIto_formula_ae_of_partition_limits f X t T I Q
      hendpoint htime hspace hquadratic hremainder
  · intro hformula
    have hconstant : TendstoInMeasure P
        (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
        Filter.atTop
        (fun omega => f t (X t omega) - f 0 (X 0 omega)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => hendpoint) (by
        filter_upwards with omega
        exact tendsto_const_nhds)
    have hraw := ((hconstant.sub_real_noMeas htime).sub_real_noMeas
      hquadratic).sub_real_noMeas hremainder
    have hspace : TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop
        (fun omega =>
          (f t (X t omega) - f 0 (X 0 omega) - T omega - Q omega) - 0) := by
      apply hraw.congr_left
      intro n
      filter_upwards with omega
      have hdecomp :=
        generalIto_uniformPartition_decomposition f X t n omega
      linarith
    apply hspace.congr_right
    filter_upwards [hformula] with omega homega
    linarith
/-- Once the other three partition terms converge, the exact decomposition
itself constructs the `dX`-sum limit.  This is useful when the theorem only
needs the stochastic first-order term existentially: its canonical value is
the endpoint increment minus the time and quadratic limits. -/
theorem generalIto_exists_space_limit_and_formula
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          T omega + I omega + Q omega := by
  let I : W → ℝ := fun omega =>
    f t (X t omega) - f 0 (X 0 omega) - T omega - Q omega
  have hformula : ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        T omega + I omega + Q omega := by
    filter_upwards with omega
    simp only [I]
    ring
  exact ⟨I, (generalIto_formula_ae_iff_space_limit
    f X t T I Q hendpoint htime hquadratic hremainder).2 hformula,
      hformula⟩
/-- The pathwise time integral appearing in the general Itô formula. -/
@[expose] noncomputable def generalItoTimeIntegral
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoTimeDerivative f s (X s.toNNReal omega)
/-- The pathwise diffusion-weighted second-order integral appearing in the
general Itô formula. -/
@[expose] noncomputable def generalItoQuadraticIntegral
    (f : ℝ → ℝ → ℝ) (X σ : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoSpaceSecondDerivative f s (X s.toNNReal omega) *
      (σ s.toNNReal omega) ^ 2
/-- The second-order Taylor residual in the state coordinate. -/
@[expose] noncomputable def itoStateTaylorRemainder
    (f : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  f x₁ - f x₀ - deriv f x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x₁ - x₀) ^ 2
omit   [MeasurableSpace W]  in
theorem itoStateTaylorRemainder_eq_itoTaylorRemainder
    (f : ℝ → ℝ) (x₀ x₁ : ℝ) :
    itoStateTaylorRemainder f x₀ x₁ =
      itoTaylorRemainder f x₀ x₁ := by
  unfold itoStateTaylorRemainder itoTaylorRemainder
  ring
/-- Accumulated second-order state residual along the uniform partition. -/
@[expose] noncomputable def itoStateTaylorRemainderApprox
    (f : ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoStateTaylorRemainder f
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)
/-- The accumulated state-only Taylor residual is invariant almost everywhere
under fixed-time modification of the process. -/
theorem itoStateTaylorRemainderApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    itoStateTaylorRemainderApprox f X t n =ᵐ[P]
      itoStateTaylorRemainderApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold itoStateTaylorRemainderApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]
end StochasticCalculus
