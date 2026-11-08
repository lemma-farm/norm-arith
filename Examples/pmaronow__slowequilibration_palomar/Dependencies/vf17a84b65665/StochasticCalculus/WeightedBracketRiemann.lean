/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.StochasticCalculus.ItoFormulaGeneral
public import Mathlib.Order.Interval.Set.Union
set_option autoImplicit false
@[expose] public section
/-!
# Weighted bracket Riemann sums

Uniform half-open partitions integrate continuous random weights against the
absolutely continuous bracket of a natural Itô process.  Combined with the
two-scale completed-cell comparison, this closes diffusion-weighted
quadratic variation for the natural stochastic-integral component.
-/
public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal
noncomputable section
namespace StochasticCalculus
/-- A quadratic partition sum whose state-dependent weight is sampled from
`Z`, while the squared increments are sampled from `M`.  This separates the
state process from its stochastic-integral component during drift removal. -/
@[expose] noncomputable def generalItoMixedQuadraticApprox
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / 2 : ℝ) *
      itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega) *
      (M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega) ^ 2
/-- The coarse-step counterpart of `generalItoMixedQuadraticApprox`. -/
noncomputable def generalItoMixedQuadraticCompletedStepApprox
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n k : ℕ) (omega : W) : ℝ :=
  ∑ j ∈ Finset.range k,
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t k j : ℝ)
      (Z (uniformPartitionTime t k j) omega)) *
    (quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k (j + 1)) omega -
      quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k j) omega)
/-- With a continuous second derivative, the mixed quadratic approximation sum
is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_generalItoMixedQuadraticApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoMixedQuadraticApprox f Z M t n) P := by
  unfold generalItoMixedQuadraticApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega) *
        (M (uniformPartitionTime t n (i + 1)) omega -
          M (uniformPartitionTime t n i) omega) ^ 2) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    have hpair : AEStronglyMeasurable
        (fun omega => ((uniformPartitionTime t n i : ℝ),
          Z (uniformPartitionTime t n i) omega)) P :=
      aestronglyMeasurable_const.prodMk
        (hZmeas (uniformPartitionTime t n i))
    have hweight : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) P :=
      hsecond.comp_aestronglyMeasurable hpair
    have hincrement : AEStronglyMeasurable
        (fun omega => M (uniformPartitionTime t n (i + 1)) omega -
          M (uniformPartitionTime t n i) omega) P :=
      (hMmeas (uniformPartitionTime t n (i + 1))).sub
        (hMmeas (uniformPartitionTime t n i))
    exact (aestronglyMeasurable_const.mul hweight).mul
      (hincrement.pow 2)
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]
/-- If the second-derivative weights of the two grids differ by at most `K` on
overlapping cells, the mixed quadratic sum and its completed-step version
differ by at most `½ K` times the quadratic sum of `M`. -/
theorem abs_generalItoMixedQuadraticApprox_sub_completedStep_le_of_blockWeight
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (ht : 0 < t) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (K : ℝ)
    (omega : W)
    (hweight : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < uniformPartitionTime t n (i + 1) ∧
        uniformPartitionTime t n (i + 1) ≤
          uniformPartitionTime t k (j + 1) →
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega) -
        itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
          (Z (uniformPartitionTime t k j) omega)| ≤ K) :
    |generalItoMixedQuadraticApprox f Z M t n omega -
      generalItoMixedQuadraticCompletedStepApprox f Z M t n k omega| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox M t n omega := by
  unfold generalItoMixedQuadraticApprox
  unfold generalItoMixedQuadraticCompletedStepApprox
  apply abs_weightedQuadraticVariation_sub_completedBlocks_le
    M t n k
      (fun i omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega))
      (fun j omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (Z (uniformPartitionTime t k j) omega))
      ((1 / 2 : ℝ) * K) omega
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hr0 : 0 < uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    positivity
  have hrt : uniformPartitionTime t n (i + 1) ≤ t :=
    (uniformPartitionTime_mem_Icc_of_le t hn hi1).2
  have hstep := abs_sub_uniformPartition_rightEndpoint_step_sum_le
    t (uniformPartitionTime t n (i + 1)) k hk hr0 hrt
      (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega))
      (fun j => itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (Z (uniformPartitionTime t k j) omega)) K
      (fun j hj hactive => hweight i hi j hj hactive)
  have hsum :
      (∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t k j : ℝ)
            (Z (uniformPartitionTime t k j) omega)
        else 0) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
            (Z (uniformPartitionTime t k j) omega)
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    split_ifs <;> simp
  rw [hsum, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left hstep (by norm_num)
/-- Along a path continuous on `[0, t]`, the gap between the mixed quadratic sum
and its completed-step version is eventually at most `½ K` times the
quadratic sum of `M`, for every positive `K`. -/
theorem generalItoMixedQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (ht : 0 < t) (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => Z s omega) (Set.Icc 0 t)) :
    ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
      |generalItoMixedQuadraticApprox f Z M t (n + 1) omega -
        generalItoMixedQuadraticCompletedStepApprox
          f Z M t (n + 1) (k + 1) omega| ≤
        (1 / 2 : ℝ) * K *
          quadraticVariationApprox M t (n + 1) omega := by
  intro K hK
  obtain ⟨N, hN⟩ := generalItoSecondDerivative_activeBlockWeight_eventually_small
    f Z t omega hsecond hpath K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  apply abs_generalItoMixedQuadraticApprox_sub_completedStep_le_of_blockWeight
    f Z M t ht (n + 1) (k + 1) (Nat.zero_lt_succ n)
      (Nat.zero_lt_succ k) K omega
  intro i hi j hj hactive
  exact (hN k n hk hn i hi j hj hactive).le
theorem
    IsContinuousProcessModification.generalItoMixedQuadraticApprox_sub_completedStep_eventually_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {Z Y M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification Z Y P)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2)) :
    ∀ᵐ omega ∂P, ∀ K : ℝ, 0 < K → ∃ N : ℕ,
      ∀ k n, N ≤ k → N ≤ n →
        |generalItoMixedQuadraticApprox f Z M t (n + 1) omega -
          generalItoMixedQuadraticCompletedStepApprox
            f Z M t (n + 1) (k + 1) omega| ≤
          (1 / 2 : ℝ) * K *
            quadraticVariationApprox M t (n + 1) omega := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid]
    with omega hcontinuous hagree
  intro K hK
  obtain ⟨N, hbound⟩ :=
    generalItoMixedQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
      f Y M t ht omega hsecond hcontinuous.continuousOn K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  have hfine : generalItoMixedQuadraticApprox f Z M t (n + 1) omega =
      generalItoMixedQuadraticApprox f Y M t (n + 1) omega := by
    unfold generalItoMixedQuadraticApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hagree n i]
  have hcoarse :
      generalItoMixedQuadraticCompletedStepApprox
          f Z M t (n + 1) (k + 1) omega =
        generalItoMixedQuadraticCompletedStepApprox
          f Y M t (n + 1) (k + 1) omega := by
    unfold generalItoMixedQuadraticCompletedStepApprox
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hagree k j]
  rw [hfine, hcoarse]
  exact hbound k n hk hn
/-- Cauchy–Schwarz for uniform-partition increments: the sum of products of
absolute increments is at most the square root of the product of the two
quadratic sums. -/
theorem sum_abs_uniformPartition_increment_mul_le_sqrt
    {W : Type*} [MeasurableSpace W]
    (A M : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      |A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega| *
      |M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega|) ≤
      √(quadraticVariationApprox A t n omega *
        quadraticVariationApprox M t n omega) := by
  apply Real.le_sqrt_of_sq_le
  unfold quadraticVariationApprox
  simpa only [sq_abs] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (fun i => |A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega|)
      (fun i => |M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega|))
/-- Adding a process `A` to `M` changes the mixed quadratic sum by at most `½ K`
times the quadratic sum of `A` plus twice the Cauchy–Schwarz cross term. -/
theorem abs_generalItoMixedQuadraticApprox_add_sub_le
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z A M : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) (K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ i ∈ Finset.range n,
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega)| ≤ K) :
    |generalItoMixedQuadraticApprox f Z
        (fun s omega => A s omega + M s omega) t n omega -
      generalItoMixedQuadraticApprox f Z M t n omega| ≤
      (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t n omega +
          2 * √(quadraticVariationApprox A t n omega *
            quadraticVariationApprox M t n omega)) := by
  have hdiff :
      generalItoMixedQuadraticApprox f Z
          (fun s omega => A s omega + M s omega) t n omega -
        generalItoMixedQuadraticApprox f Z M t n omega =
      ∑ i ∈ Finset.range n,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) *
        ((A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) ^ 2 +
          2 * (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) *
            (M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega)) := by
    unfold generalItoMixedQuadraticApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) *
        ((A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) ^ 2 +
          2 * (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) *
            (M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) * K *
          ((A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega) ^ 2 +
            2 * |A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega| *
              |M (uniformPartitionTime t n (i + 1)) omega -
                M (uniformPartitionTime t n i) omega|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        (1 / 2 : ℝ) *
            |itoSpaceSecondDerivative f
              (uniformPartitionTime t n i : ℝ)
              (Z (uniformPartitionTime t n i) omega)| *
            |(A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2 +
              2 * (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) *
                (M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega)| ≤
          (1 / 2 : ℝ) * K *
            (|(A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2| +
              |2 * (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) *
                (M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega)|) := by
            gcongr
            · exact hweight i hi
            · exact abs_add_le _ _
        _ = _ := by
          rw [abs_sq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t n omega +
          2 * ∑ i ∈ Finset.range n,
            |A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega| *
            |M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega|) := by
      unfold quadraticVariationApprox
      calc
        _ = ∑ i ∈ Finset.range n,
            ((1 / 2 : ℝ) * K *
              (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2 +
            (1 / 2 : ℝ) * K *
              (2 * |A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega| *
                |M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega|)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
        _ = (∑ i ∈ Finset.range n,
              (1 / 2 : ℝ) * K *
                (A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega) ^ 2) +
            ∑ i ∈ Finset.range n,
              (1 / 2 : ℝ) * K *
                (2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) :=
              Finset.sum_add_distrib
        _ = (1 / 2 : ℝ) * K *
              (∑ i ∈ Finset.range n,
                (A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega) ^ 2) +
            (1 / 2 : ℝ) * K *
              (∑ i ∈ Finset.range n,
                2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) := by
              rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := by
          have hsum_two :
              (∑ i ∈ Finset.range n,
                2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) =
                2 * ∑ i ∈ Finset.range n,
                  |A (uniformPartitionTime t n (i + 1)) omega -
                    A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          rw [hsum_two]
          ring
    _ ≤ _ := by
      gcongr
      exact sum_abs_uniformPartition_increment_mul_le_sqrt A M t n omega
/-- Adding a process whose quadratic sums vanish almost surely does not change
the limit in probability of the mixed quadratic sum. -/
theorem generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z A M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hAmeas : ∀ s, AEStronglyMeasurable (A s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (q : W → ℝ)
    (hA : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n => quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0))
    (hM : TendstoInMeasure P
      (fun n => quadraticVariationApprox M t (n + 1))
      Filter.atTop q)
    (hweight : ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ n i : ℕ, i ≤ n + 1 →
        |itoSpaceSecondDerivative f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (Z (uniformPartitionTime t (n + 1) i) omega)| ≤ K) :
    TendstoInMeasure P
      (fun n omega =>
        generalItoMixedQuadraticApprox f Z
            (fun s omega => A s omega + M s omega) t (n + 1) omega -
          generalItoMixedQuadraticApprox f Z M t (n + 1) omega)
      Filter.atTop (fun _ => 0) := by
  have hdiffmeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        generalItoMixedQuadraticApprox f Z
            (fun s omega => A s omega + M s omega) t (n + 1) omega -
          generalItoMixedQuadraticApprox f Z M t (n + 1) omega) P := by
    intro n
    exact (aestronglyMeasurable_generalItoMixedQuadraticApprox
      f hsecond Z (fun s omega => A s omega + M s omega)
        hZmeas (fun s => (hAmeas s).add (hMmeas s)) t (n + 1)).sub
      (aestronglyMeasurable_generalItoMixedQuadraticApprox
        f hsecond Z M hZmeas hMmeas t (n + 1))
  rw [exists_seq_tendstoInMeasure_atTop_iff hdiffmeas]
  intro ns hns
  obtain ⟨r, hr, hMomega⟩ :=
    (hM.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨r, hr, ?_⟩
  filter_upwards [hA, hMomega, hweight]
    with omega hAomega hMlimit homega
  obtain ⟨K, hK, hKbound⟩ := homega
  have hindices : StrictMono (ns ∘ r) := hns.comp hr
  have hAfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox A t (ns (r i) + 1) omega)
      Filter.atTop (nhds 0) := by
    convert hAomega.comp hindices.tendsto_atTop using 1
    funext i
    rfl
  have hMfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox M t (ns (r i) + 1) omega)
      Filter.atTop (nhds (q omega)) := by
    simpa only [Function.comp_apply] using hMlimit
  have hsqrt : Filter.Tendsto
      (fun i => √(quadraticVariationApprox A t (ns (r i) + 1) omega *
        quadraticVariationApprox M t (ns (r i) + 1) omega))
      Filter.atTop (nhds 0) := by
    have hraw := (hAfinal.mul hMfinal).sqrt
    simpa only [zero_mul, Real.sqrt_zero] using hraw
  have hupper : Filter.Tendsto
      (fun i => (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t (ns (r i) + 1) omega +
          2 * √(quadraticVariationApprox A t (ns (r i) + 1) omega *
            quadraticVariationApprox M t (ns (r i) + 1) omega)))
      Filter.atTop (nhds 0) := by
    have htwo : Filter.Tendsto (fun _ : ℕ => (2 : ℝ))
        Filter.atTop (nhds 2) := tendsto_const_nhds
    have hscale : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ) * K)
        Filter.atTop (nhds ((1 / 2 : ℝ) * K)) := tendsto_const_nhds
    have hinside := hAfinal.add (htwo.mul hsqrt)
    have hscaled := hscale.mul hinside
    simpa only [mul_zero, add_zero] using hscaled
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero (g := fun i => (1 / 2 : ℝ) * K *
      (quadraticVariationApprox A t (ns (r i) + 1) omega +
        2 * √(quadraticVariationApprox A t (ns (r i) + 1) omega *
          quadraticVariationApprox M t (ns (r i) + 1) omega)))
  · intro i
    exact abs_nonneg _
  · intro i
    apply abs_generalItoMixedQuadraticApprox_add_sub_le
      f Z A M t (ns (r i) + 1) omega K hK
    intro j hj
    apply hKbound (ns (r i)) j
    exact (Nat.le_add_right j 1).trans (Finset.mem_range.mp hj)
  · exact hupper
/-- The difference of the integrals over `(z, b]` and `(z, a]` is the integral
over `(a, b]`. -/
theorem integral_Ioc_sub_integral_Ioc_eq_integral_Ioc
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} {q : α → ℝ} {z a b t : α}
    (hza : z ≤ a) (hab : a ≤ b) (hbt : b ≤ t)
    (hq : IntegrableOn q (Ioc z t) μ) :
    (∫ s in Ioc z b, q s ∂μ) - (∫ s in Ioc z a, q s ∂μ) =
      ∫ s in Ioc a b, q s ∂μ := by
  have hsmall : Ioc z b ⊆ Ioc z t := Ioc_subset_Ioc_right hbt
  have hsub : Ioc z a ⊆ Ioc z b := Ioc_subset_Ioc_right hab
  have hdiff : Ioc z b \ Ioc z a = Ioc a b := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_Ioc]
    grind
  rw [← hdiff]
  exact (setIntegral_sdiff measurableSet_Ioc (hq.mono_set hsmall) hsub).symm
/-- Consecutive half-open intervals of a monotone sequence tile `(a 0, a N]`. -/
theorem biUnion_Ioc_succ_eq_Ioc
    {α : Type*} [LinearOrder α] (a : ℕ → α) (ha : Monotone a) (N : ℕ) :
    (⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1))) = Ioc (a 0) (a N) := by
  apply Subset.antisymm
  · rw [iUnion_subset_iff]
    intro i
    rw [iUnion_subset_iff]
    intro hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact Ioc_subset_Ioc (ha (Nat.zero_le i)) (ha (Nat.succ_le_iff.mpr hiN))
  · exact Ioc_subset_biUnion_Ioc N a
/-- Given the before-stop quadratic-variation limits of `M` and convergence of
the bracket-step sums, the mixed quadratic sum converges in probability to
the same limit. -/
theorem generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (ht : 0 < t) (Q : ℝ≥0 → W → ℝ) (G : W → ℝ)
    (hbefore : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox M t (n + 1) a)
      Filter.atTop (Q a))
    (hG : TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G)
    (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification Z Y P) :
    TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f Z M t (n + 1))
      Filter.atTop G := by
  let F : ℕ → ℕ → W → ℝ := fun k n =>
    generalItoMixedQuadraticCompletedStepApprox
      f Z M t (n + 1) (k + 1)
  let Gk : ℕ → W → ℝ := fun k omega => ∑ i ∈ Finset.range (k + 1),
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t (k + 1) i : ℝ)
      (Z (uniformPartitionTime t (k + 1) i) omega)) *
    (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
      Q (uniformPartitionTime t (k + 1) i) omega)
  have hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (Gk k) := by
    intro k
    unfold F Gk generalItoMixedQuadraticCompletedStepApprox
    apply tendstoInMeasure_finset_sum_mul_fixed_real (Finset.range (k + 1))
      (fun i n omega =>
        quadraticVariationBeforeStopApprox M t (n + 1)
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          quadraticVariationBeforeStopApprox M t (n + 1)
            (uniformPartitionTime t (k + 1) i) omega)
      (fun i omega =>
        Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega)
      (fun i omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t (k + 1) i : ℝ)
        (Z (uniformPartitionTime t (k + 1) i) omega))
    · intro i hi
      have hi1 : i + 1 ≤ k + 1 := Finset.mem_range.mp hi
      have hi0 : i ≤ k + 1 := (Nat.le_add_right i 1).trans hi1
      exact (hbefore (uniformPartitionTime t (k + 1) (i + 1))
        (uniformPartitionTime_mem_Icc_of_le t
          (Nat.zero_lt_succ k) hi1).2).sub_real_noMeas
        (hbefore (uniformPartitionTime t (k + 1) i)
          (uniformPartitionTime_mem_Icc_of_le t
            (Nat.zero_lt_succ k) hi0).2)
    · intro i _hi n
      exact (aestronglyMeasurable_quadraticVariationBeforeStopApprox
        hMmeas t (n + 1)
          (uniformPartitionTime t (k + 1) (i + 1))).sub
        (aestronglyMeasurable_quadraticVariationBeforeStopApprox
          hMmeas t (n + 1) (uniformPartitionTime t (k + 1) i))
    · intro i _hi
      have hpair : AEStronglyMeasurable
          (fun omega => ((uniformPartitionTime t (k + 1) i : ℝ),
            Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.prodMk
          (hZmeas (uniformPartitionTime t (k + 1) i))
      exact aestronglyMeasurable_const.mul
        (hsecond.comp_aestronglyMeasurable hpair)
  have hq : TendstoInMeasure P
      (fun n => quadraticVariationApprox M t (n + 1))
      Filter.atTop (Q t) := by
    apply (hbefore t le_rfl).congr_left
    intro n
    filter_upwards with omega
    unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]
  apply TendstoInMeasure.of_ae_two_scale_uniform_control
    (P := P)
    (f := fun n => generalItoMixedQuadraticApprox f Z M t (n + 1))
    (q := fun n => quadraticVariationApprox M t (n + 1))
    (F := F) (G := Gk) (qlim := Q t)
  · intro n
    exact aestronglyMeasurable_generalItoMixedQuadraticApprox
      f hsecond Z M hZmeas hMmeas t (n + 1)
  · exact hFG
  · simpa only [Gk] using hG
  · exact hq
  · intro n omega
    exact quadraticVariationApprox_nonneg M t (n + 1) omega
  · have hbound :=
      hmod.generalItoMixedQuadraticApprox_sub_completedStep_eventually_le
        (M := M) f t ht hsecond
    filter_upwards [hbound] with omega homega
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := homega (2 * epsilon)
      (mul_pos (by norm_num) hepsilon)
    refine ⟨N, fun k n hk hn => ?_⟩
    have hraw := hN k n hk hn
    simpa only [F, Real.norm_eq_abs, mul_assoc,
      show (1 / 2 : ℝ) * (2 * epsilon) = epsilon by ring] using hraw
/-- The pathwise continuous-weight integral against a selected nonnegative
bracket density on nonnegative time. -/
noncomputable def generalItoQuadraticBracketIntegral
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Y : ℝ≥0 → W → ℝ)
    (u : ℝ≥0 × W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) t,
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
      (u (s, omega)) ^ 2 ∂nonnegativeLebesgueMeasure
/-- The bracket integral with the uncurried diffusion coefficient equals the
quadratic integral of the general Itô formula. -/
theorem generalItoQuadraticBracketIntegral_uncurry_eq
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Y sigma : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    generalItoQuadraticBracketIntegral f Y (Function.uncurry sigma) t omega =
      generalItoQuadraticIntegral f Y sigma t omega := by
  unfold generalItoQuadraticBracketIntegral generalItoQuadraticIntegral
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,
      map_nonnegativeLebesgueMeasure_restrict_Ioc t⟩
  have hchange := hpres.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun r : ℝ =>
      ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r (Y r.toNNReal omega)) *
        (sigma r.toNNReal omega) ^ 2)
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) =
        ∫ r in Set.Ioc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 := by
      simpa [Function.uncurry] using hchange
    _ = ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 :=
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
    _ = (1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          itoSpaceSecondDerivative f r (Y r.toNNReal omega) *
            (sigma r.toNNReal omega) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext r
      ring
/-- The quadratic sums of an Itô process with given characteristics converge in
probability to the integrated square of the diffusion coefficient. -/
theorem quadraticVariation_tendstoInMeasure_of_characteristics
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (X mu sigma J : ℝ≥0 → W → ℝ)
    (hJmeas : ∀ s, AEStronglyMeasurable (J s) P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ t omega, IntegrableOn
      (fun s : ℝ => mu s.toNNReal omega) (Set.Icc 0 (t : ℝ)))
    (hdecomp : ∀ s, X s =ᵐ[P] fun omega =>
      X 0 omega + integratedDrift mu s omega + J s omega)
    (hbefore : ∀ T a, TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a)
      Filter.atTop (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) := by
  let A : ℝ≥0 → W → ℝ := integratedDrift mu
  let Q : W → ℝ := fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
    (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := by
    intro s
    exact (stronglyMeasurable_integratedDrift hmuMeas s).aestronglyMeasurable
  have hAqv : HasQuadraticVariationInProbabilityAt A P t (fun _ => 0) := by
    exact quadraticVariation_integratedDrift_inProbability
      hmuMeas t (hmuInt t)
  have hJqv : HasQuadraticVariationInProbabilityAt J P t Q := by
    unfold HasQuadraticVariationInProbabilityAt
    have hraw : TendstoInMeasure P
        (fun n => quadraticVariationBeforeStopApprox J t (n + 1) t)
        Filter.atTop Q := by
      simpa only [Q, min_self] using hbefore t t
    apply hraw.congr_left
    intro n
    filter_upwards with omega
    unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]
  have hadd : HasQuadraticVariationInProbabilityAt
      (fun s omega => A s omega + J s omega) P t Q :=
    hAqv.add_of_left_zero_of_aestronglyMeasurable
      hJqv hAmeas hJmeas
  have hgrid := fixedTime_ae_eq_uniformPartitions hdecomp t
  have heq : ∀ n, quadraticVariationApprox X t (n + 1) =ᵐ[P]
      quadraticVariationApprox (fun s omega => A s omega + J s omega)
        t (n + 1) := by
    intro n
    filter_upwards [hgrid] with omega homega
    unfold quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [homega n i, homega n (i + 1)]
    ring
  unfold HasQuadraticVariationInProbabilityAt at hadd
  apply hadd.congr_left
  intro n
  exact (heq n).symm
end StochasticCalculus
