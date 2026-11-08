import Examples.scottnarmstrong__CoarseGraining.Dependencies.v1297d2aae338.Homogenization.Probability.IndependentSums.GammaSigma.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
/-- The explicit `Γ_σ` moment-growth triangle constant obtained by combining
the Chapter 4 tail/moment bridge with the independent-sums `Γ_σ` triangle
inequality. -/
noncomputable def gammaMomentTriangleConst (σ : ℝ) : ℝ :=
  gammaMomentConst σ * Real.exp 1 * gammaTriangleConst σ
lemma gammaTriangleConst_pos {σ : ℝ} : 0 < gammaTriangleConst σ := by
  have hGrowthPos : 0 < gammaGrowthConst σ := lt_of_lt_of_le zero_lt_two (two_le_gammaGrowthConst σ)
  dsimp [gammaTriangleConst]
  positivity
lemma gammaMomentTriangleConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gammaMomentTriangleConst σ := by
  have hMomentConst : 0 < gammaMomentConst σ := gammaMomentConst_pos hσ
  have hTrianglePos : 0 < gammaTriangleConst σ := gammaTriangleConst_pos
  dsimp [gammaMomentTriangleConst]
  positivity
/-- Finite-family generalized triangle inequality in witness-level
`Γ_σ` moment-growth form. -/
theorem hasGammaMomentGrowthWith_finset_sum
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    HasGammaMomentGrowthWith μ σ (fun ω => Finset.sum s (fun i => X i ω))
      (gammaMomentTriangleConst σ * Finset.sum s a) := by
  have hTail : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (Real.exp 1 * a i) := by
    intro i hi
    exact isBigO_gammaSigma_of_hasGammaMomentGrowthWith
      (μ := μ) (X := X i) (M := a i) (σ := σ) hσ (ha i hi) (hX i hi)
  have hTailSum :
      IsBigO μ (gammaSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
        (gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i)) := by
    refine isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := μ) (s := s) (X := X) (a := fun i => Real.exp 1 * a i) (σ := σ)
      hσ hs ?_ hTail hXm
    intro i hi
    exact mul_pos (by positivity) (ha i hi)
  have hScaledSum_pos : 0 < Finset.sum s (fun i => Real.exp 1 * a i) := by
    rcases hs with ⟨i₀, hi₀⟩
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      exact mul_nonneg (by positivity : 0 ≤ Real.exp 1) (ha i hi).le
    · refine ⟨i₀, hi₀, ?_⟩
      exact mul_pos (by positivity) (ha i₀ hi₀)
  have hTriangle_pos : 0 < gammaTriangleConst σ := gammaTriangleConst_pos
  have hTailScale_pos :
      0 < gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i) := by
    exact mul_pos hTriangle_pos hScaledSum_pos
  have hSum_meas :
      AEMeasurable (fun ω => Finset.sum s (fun i => X i ω)) μ :=
    (Finset.measurable_sum (s := s) fun i hi => hXm i hi).aemeasurable
  have hMoment :=
    hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := fun ω => Finset.sum s (fun i => X i ω))
      (K := gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i))
      (σ := σ) hσ hTailScale_pos hSum_meas hTailSum
  have hScaledSum :
      Finset.sum s (fun i => Real.exp 1 * a i) = Real.exp 1 * Finset.sum s a := by
    rw [← Finset.mul_sum]
  convert hMoment using 1
  rw [gammaMomentTriangleConst, hScaledSum]
  ring
/-- Average version of the witness-level `Γ_σ` moment-growth triangle
inequality. -/
theorem hasGammaMomentGrowthWith_finsetAverage
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    HasGammaMomentGrowthWith μ σ
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (gammaMomentTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  have hTail : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (Real.exp 1 * a i) := by
    intro i hi
    exact isBigO_gammaSigma_of_hasGammaMomentGrowthWith
      (μ := μ) (X := X i) (M := a i) (σ := σ) hσ (ha i hi) (hX i hi)
  have hTailAvg :
      IsBigO μ (gammaSigma σ)
        (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
        (gammaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s (fun i => Real.exp 1 * a i))) := by
    refine isBigO_finsetAverage_of_isBigO_gammaSigma
      (μ := μ) (s := s) (X := X) (a := fun i => Real.exp 1 * a i) (σ := σ)
      hσ hs ?_ hTail hXm
    intro i hi
    exact mul_pos (by positivity) (ha i hi)
  have hScaledSum_pos : 0 < Finset.sum s (fun i => Real.exp 1 * a i) := by
    rcases hs with ⟨i₀, hi₀⟩
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      exact mul_nonneg (by positivity : 0 ≤ Real.exp 1) (ha i hi).le
    · refine ⟨i₀, hi₀, ?_⟩
      exact mul_pos (by positivity) (ha i₀ hi₀)
  have hCard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have hAvgScale_pos :
      0 < ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => Real.exp 1 * a i) := by
    exact mul_pos (inv_pos.mpr hCard_pos) hScaledSum_pos
  have hTriangle_pos : 0 < gammaTriangleConst σ := gammaTriangleConst_pos
  have hTailScale_pos :
      0 < gammaTriangleConst σ *
        (((s.card : ℝ)⁻¹) * Finset.sum s (fun i => Real.exp 1 * a i)) := by
    exact mul_pos hTriangle_pos hAvgScale_pos
  have hSum_meas : Measurable (fun ω => Finset.sum s (fun i => X i ω)) :=
    Finset.measurable_sum (s := s) fun i hi => hXm i hi
  have hAvg_meas :
      AEMeasurable (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω)) μ :=
    (measurable_const.mul hSum_meas).aemeasurable
  have hMoment :=
    hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (K := gammaTriangleConst σ *
        (((s.card : ℝ)⁻¹) * Finset.sum s (fun i => Real.exp 1 * a i)))
      (σ := σ) hσ hTailScale_pos hAvg_meas hTailAvg
  have hScaledSum :
      Finset.sum s (fun i => Real.exp 1 * a i) = Real.exp 1 * Finset.sum s a := by
    rw [← Finset.mul_sum]
  convert hMoment using 1
  rw [gammaMomentTriangleConst, hScaledSum]
  ring
/-- Finite-family generalized triangle inequality for existential
`Γ_σ` moment-growth witnesses. -/
theorem hasGammaMomentGrowth_finset_sum
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs : s.Nonempty)
    (hX : ∀ i ∈ s, HasGammaMomentGrowth μ σ (X i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    HasGammaMomentGrowth μ σ (fun ω => Finset.sum s (fun i => X i ω)) := by
  classical
  have hChoice : ∀ i ∈ s, ∃ a, 0 < a ∧ HasGammaMomentGrowthWith μ σ (X i) a := by
    intro i hi
    simpa [HasGammaMomentGrowth] using hX i hi
  let a : ι → ℝ := fun i =>
    if hi : i ∈ s then Classical.choose (hChoice i hi) else 1
  have ha : ∀ i ∈ s, 0 < a i := by
    intro i hi
    simpa [a, hi] using (Classical.choose_spec (hChoice i hi)).1
  have hXa : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i) := by
    intro i hi
    simpa [a, hi] using (Classical.choose_spec (hChoice i hi)).2
  have hSum_pos : 0 < Finset.sum s a := by
    rcases hs with ⟨i₀, hi₀⟩
    exact Finset.sum_pos' (fun i hi => (ha i hi).le) ⟨i₀, hi₀, ha i₀ hi₀⟩
  refine ⟨gammaMomentTriangleConst σ * Finset.sum s a,
    mul_pos (gammaMomentTriangleConst_pos hσ) hSum_pos, ?_⟩
  exact hasGammaMomentGrowthWith_finset_sum
    (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hXa hXm
/-- Average version of the existential `Γ_σ` moment-growth triangle
inequality. -/
theorem hasGammaMomentGrowth_finsetAverage
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs : s.Nonempty)
    (hX : ∀ i ∈ s, HasGammaMomentGrowth μ σ (X i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    HasGammaMomentGrowth μ σ
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω)) := by
  classical
  have hChoice : ∀ i ∈ s, ∃ a, 0 < a ∧ HasGammaMomentGrowthWith μ σ (X i) a := by
    intro i hi
    simpa [HasGammaMomentGrowth] using hX i hi
  let a : ι → ℝ := fun i =>
    if hi : i ∈ s then Classical.choose (hChoice i hi) else 1
  have ha : ∀ i ∈ s, 0 < a i := by
    intro i hi
    simpa [a, hi] using (Classical.choose_spec (hChoice i hi)).1
  have hXa : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i) := by
    intro i hi
    simpa [a, hi] using (Classical.choose_spec (hChoice i hi)).2
  have hSum_pos : 0 < Finset.sum s a := by
    rcases hs with ⟨i₀, hi₀⟩
    exact Finset.sum_pos' (fun i hi => (ha i hi).le) ⟨i₀, hi₀, ha i₀ hi₀⟩
  have hCard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have hAvgScale_pos : 0 < ((s.card : ℝ)⁻¹) * Finset.sum s a := by
    exact mul_pos (inv_pos.mpr hCard_pos) hSum_pos
  refine ⟨gammaMomentTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a),
    mul_pos (gammaMomentTriangleConst_pos hσ) hAvgScale_pos, ?_⟩
  exact hasGammaMomentGrowthWith_finsetAverage
    (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hXa hXm
/-- Event indicators belong to the stretched-exponential class with the
natural logarithmic scale from the Chapter 4 notes. -/
theorem isBigOWith_gammaSigma_indicator
    {E : Set Ω} {σ : ℝ}
    (hσ : 0 < σ) (hE_pos : 0 < μ.real E) (hE_lt_one : μ.real E < 1) :
    IsBigOWith μ (gammaSigma σ) (E.indicator fun _ => (1 : ℝ))
      (gammaIndicatorScale σ (μ.real E)) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let p : ℝ := μ.real E
  let B : ℝ := -Real.log p
  let A : ℝ := gammaIndicatorScale σ p
  have hp_pos : 0 < p := hE_pos
  have hB_pos : 0 < B := by
    dsimp [B, p]
    have hlog_neg : Real.log (μ.real E) < 0 := Real.log_neg hE_pos hE_lt_one
    linarith
  have hA_pos : 0 < A := by
    dsimp [A, gammaIndicatorScale]
    exact Real.rpow_pos_of_pos hB_pos _
  have hAt_nonneg : 0 ≤ A * t := mul_nonneg hA_pos.le (le_trans zero_le_one ht)
  by_cases hcut : A * t < 1
  · have hset : upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) = E := by
      ext ω
      by_cases hω : ω ∈ E
      · simp [upperTailEvent, hω, hcut]
      · simp [upperTailEvent, hω, not_lt.mpr hAt_nonneg]
    rw [hset]
    have hcut' : t < B ^ σ⁻¹ := by
      have hBroot_pos : 0 < B ^ σ⁻¹ := Real.rpow_pos_of_pos hB_pos _
      have hAt_div : A * t = t / (B ^ σ⁻¹) := by
        dsimp [A, gammaIndicatorScale]
        rw [Real.rpow_neg hB_pos.le, mul_comm, div_eq_mul_inv]
      rw [hAt_div, div_lt_iff₀ hBroot_pos] at hcut
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcut
    have htail : t ^ σ < B := by
      exact (Real.lt_rpow_inv_iff_of_pos (le_trans zero_le_one ht) hB_pos.le hσ).1 hcut'
    have hp_tail : p < Real.exp (-(t ^ σ)) := by
      refine (Real.log_lt_iff_lt_exp hp_pos).1 ?_
      dsimp [B, p] at htail ⊢
      linarith
    exact hp_tail.le
  · have hAt_ge : 1 ≤ A * t := le_of_not_gt hcut
    have hset : upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) = ∅ := by
      ext ω
      by_cases hω : ω ∈ E
      · simp [upperTailEvent, hω, not_lt.mpr hAt_ge]
      · simp [upperTailEvent, hω, not_lt.mpr hAt_nonneg]
    rw [hset]
    simpa using (show (0 : ℝ) ≤ Real.exp (-(t ^ σ)) by positivity)
/-- Event indicators also satisfy the symmetric `O_{Γ_σ}` relation, since the
indicator is already nonnegative. -/
theorem isBigO_gammaSigma_indicator
    {E : Set Ω} {σ : ℝ}
    (hσ : 0 < σ) (hE_pos : 0 < μ.real E) (hE_lt_one : μ.real E < 1) :
    IsBigO μ (gammaSigma σ) (E.indicator fun _ => (1 : ℝ))
      (gammaIndicatorScale σ (μ.real E)) := by
  have habs :
      (fun ω => |E.indicator (fun _ => (1 : ℝ)) ω|) =
        E.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  rw [IsBigO, habs]
  exact isBigOWith_gammaSigma_indicator (μ := μ) (E := E) (σ := σ) hσ hE_pos hE_lt_one
/-- Finite-maximum bound in the stretched-exponential class. This is the
finite-family version of the Chapter 4 maximum lemma with the note-facing
constant `(3 log N)^{1/σ}`. -/
theorem isBigOWith_gammaSigma_finset_sup'
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A σ : ℝ} [IsFiniteMeasure μ]
    (hσ : 0 < σ) (hs_card : 2 ≤ s.card)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) A) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs (fun i => X i ω))
      (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) * A) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let n : ℝ := s.card
  let L : ℝ := (3 * Real.log n) ^ σ⁻¹
  have hs_card_real : (2 : ℝ) ≤ n := by
    change (2 : ℝ) ≤ (s.card : ℝ)
    exact_mod_cast hs_card
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  have hlog_two_lt : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog_two_le : Real.log 2 ≤ Real.log n := by
    exact Real.log_le_log (by norm_num) hs_card_real
  have hone_le_two_log : 1 ≤ 2 * Real.log n := by
    nlinarith
  have hbase_one : 1 ≤ 3 * Real.log n := by
    nlinarith [hone_le_two_log]
  have hbase_nonneg : 0 ≤ 3 * Real.log n := le_trans zero_le_one hbase_one
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg hbase_nonneg _
  have hL_one : 1 ≤ L := by
    dsimp [L]
    exact Real.one_le_rpow hbase_one (inv_nonneg.mpr hσ.le)
  have hLt_one : 1 ≤ L * t := by
    nlinarith
  have hsubset :
      upperTailEvent (fun ω => s.sup' hs (fun i => X i ω)) ((L * A) * t) ⊆
        ⋃ i ∈ s, upperTailEvent (X i) (A * (L * t)) := by
    intro ω hω
    have hω' : A * (L * t) < s.sup' hs (fun i => X i ω) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hω
    rcases (Finset.lt_sup'_iff hs).1 hω' with ⟨i, hi, hiω⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hiω⟩⟩
  have hLpow : L ^ σ = 3 * Real.log n := by
    dsimp [L]
    rw [Real.rpow_inv_rpow hbase_nonneg hσ.ne']
  have hmulpow : (L * t) ^ σ = (3 * Real.log n) * t ^ σ := by
    calc
      (L * t) ^ σ = L ^ σ * t ^ σ := by
        rw [Real.mul_rpow hL_nonneg (le_trans zero_le_one ht)]
      _ = (3 * Real.log n) * t ^ σ := by
        rw [hLpow]
  have htpow_one : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ.le
  have hunion_ne_top :
      μ (⋃ i ∈ s, upperTailEvent (X i) (A * (L * t))) ≠ ⊤ :=
    measure_ne_top μ _
  calc
    μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => X i ω)) (((3 * Real.log n) ^ σ⁻¹ * A) * t))
      ≤ μ.real (⋃ i ∈ s, upperTailEvent (X i) (A * (L * t))) := by
          simpa [L, mul_assoc, mul_left_comm, mul_comm] using
            (measureReal_mono hsubset hunion_ne_top)
    _ ≤ ∑ i ∈ s, μ.real (upperTailEvent (X i) (A * (L * t))) := by
          simpa using measureReal_biUnion_finset_le s
            (fun i => upperTailEvent (X i) (A * (L * t)))
    _ ≤ ∑ _i ∈ s, Real.exp (-((L * t) ^ σ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simpa [gammaSigma, ← Real.exp_neg] using hX i hi hLt_one
    _ = n * Real.exp (-((L * t) ^ σ)) := by
          simp [n]
    _ = Real.exp (Real.log n - (L * t) ^ σ) := by
          calc
            n * Real.exp (-((L * t) ^ σ)) = Real.exp (Real.log n) * Real.exp (-((L * t) ^ σ)) := by
              rw [Real.exp_log hn_pos]
            _ = Real.exp (Real.log n + -((L * t) ^ σ)) := by
              rw [← Real.exp_add]
            _ = Real.exp (Real.log n - (L * t) ^ σ) := by
              simp [sub_eq_add_neg]
    _ ≤ Real.exp (-(t ^ σ)) := by
          refine (Real.exp_le_exp).2 ?_
          rw [hmulpow]
          nlinarith [hone_le_two_log, htpow_one]
    _ = Real.exp (-(t ^ σ)) := rfl
end
end IndependentSums
end Homogenization
