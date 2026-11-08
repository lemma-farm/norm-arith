module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.PredictableItoTime
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
public section
/-! The deterministic Volterra operator in the same predictable product L²
space used for the Itô operator. No adaptedness or integrability of a putative
solution is supplied as an existence hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PredictableDriftTime
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
/-- A globally strongly predictable representative of the actual L² class. -/
@[expose] def representative (U : PredictableProcessL2 F P) : ℝ≥0 × Ω → ℝ :=
  (lpMeas.aestronglyMeasurable U).mk (U : TimeProcessL2 P)
theorem representative_stronglyMeasurable (U : PredictableProcessL2 F P) :
    StronglyMeasurable[F.predictable] (representative U) :=
  (lpMeas.aestronglyMeasurable U).stronglyMeasurable_mk
theorem representative_ae (U : PredictableProcessL2 F P) :
    representative U =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : TimeProcessL2 P) :=
  ((lpMeas.aestronglyMeasurable U).ae_eq_mk).symm
@[expose] def primitive (H : ℝ≥0 × Ω → ℝ) (t : ℝ≥0) (omega : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t, H (s, omega) ∂nonnegativeLebesgueMeasure
/-- Deterministic integration up to time `t` preserves the full filtration. -/
theorem primitive_stronglyAdapted (H : ℝ≥0 × Ω → ℝ)
    (hH : StronglyMeasurable[F.predictable] H) : StronglyAdapted F (primitive H) := by
  have hprog : IsStronglyProgressive F (fun t omega => H (t, omega)) :=
    (show IsStronglyPredictable F (fun t omega => H (t, omega)) from hH).isStronglyProgressive
  intro t
  letI : MeasurableSpace Ω := F t
  have hpair : Measurable (fun p : ℝ≥0 × Ω =>
      ((⟨min p.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic t), p.2)) :=
    ((measurable_fst.min measurable_const).subtype_mk).prodMk measurable_snd
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω => H (min p.1 t, p.2)) :=
    (hprog t).comp_measurable hpair
  have hcut := hm.indicator ((measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ≥0) t)).preimage measurable_fst)
  have hi := hcut.integral_prod_left' (μ := nonnegativeLebesgueMeasure)
  convert hi using 1
  funext omega
  rw [primitive, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
    · simp [hs, min_eq_left hs.2]
    · simp [hs])
omit [IsProbabilityMeasure P] in
theorem integral_sq_le_measure_mul_integral_sq {A : Type*} [MeasurableSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (f : A → ℝ) (hf : MemLp f 2 mu) :
    (∫ x, f x ∂mu)^2 ≤ mu.real univ * ∫ x, f x^2 ∂mu := by
  have h1 : MemLp (fun _ : A => (1 : ℝ)) 2 mu := memLp_const 1
  have hi : inner ℝ (h1.toLp (fun _ : A => (1 : ℝ))) (hf.toLp f) = ∫ x, f x ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hf.coeFn_toLp] with x hx1 hxf
    simp only [RCLike.inner_apply, conj_trivial, hx1, hxf, one_mul, mul_one]
  have hn1 : ‖h1.toLp (fun _ : A => (1 : ℝ))‖^2 = mu.real univ := by
    rw [← SphericalAging.PredictableItoTime.integral_sq_toLp]
    simp
  have hnf := SphericalAging.PredictableItoTime.integral_sq_toLp f hf
  have hc := norm_inner_le_norm (𝕜 := ℝ) (h1.toLp (fun _ : A => (1 : ℝ))) (hf.toLp f)
  rw [hi] at hc
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hc
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, hn1, ← hnf] using hs
/-- Any integrable path has a continuous deterministic primitive. The
endpoint null-set is handled for the actual nonnegative Lebesgue measure. -/
theorem primitive_continuous (H : ℝ≥0 × Ω → ℝ) (omega : Ω)
    (hH : Integrable (fun s => H (s, omega)) nonnegativeLebesgueMeasure) :
    Continuous (fun t => primitive H t omega) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  have hlim : ∀ᵐ s ∂nonnegativeLebesgueMeasure,
      Tendsto (fun n => (Ioc (0 : ℝ≥0) (u n)).indicator (fun s => H (s, omega)) s)
        atTop (𝓝 ((Ioc (0 : ℝ≥0) t).indicator (fun s => H (s, omega)) s)) := by
    have hae : ∀ᵐ s ∂nonnegativeLebesgueMeasure, s ≠ t := by
      rw [ae_iff]
      simpa using FourPapersCommon.FilteredBrownian.nonnegativeLebesgueMeasure_singleton t
    filter_upwards [hae] with s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hs0' : 0 < s := lt_of_le_of_ne (zero_le : 0 ≤ s) (Ne.symm hs0)
      rcases lt_or_gt_of_ne hs with hst | hts
      · apply tendsto_const_nhds.congr'
        filter_upwards [hu.eventually (eventually_gt_nhds hst)] with n hn
        simp [hs0', hst.le, hn.le]
      · apply tendsto_const_nhds.congr'
        filter_upwards [hu.eventually (eventually_lt_nhds hts)] with n hn
        simp [not_le_of_gt hts, not_le_of_gt hn]
  simpa only [primitive, Function.comp_def, integral_indicator measurableSet_Ioc] using
    tendsto_integral_of_dominated_convergence (fun s => ‖H (s, omega)‖)
      (fun n => hH.aestronglyMeasurable.indicator measurableSet_Ioc) hH.norm
      (fun n => .of_forall (fun s => norm_indicator_le_norm_self _ s)) hlim
@[expose] def cutRepresentative (U : PredictableProcessL2 F P) (T : ℝ≥0) : ℝ≥0 × Ω → ℝ :=
  (FourPapersCommon.FilteredBrownian.predictableTimeFrame T).indicator (representative U)
theorem cutRepresentative_stronglyMeasurable (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    StronglyMeasurable[F.predictable] (cutRepresentative U T) :=
  (representative_stronglyMeasurable U).indicator (FourPapersCommon.FilteredBrownian.measurableSet_predictableTimeFrame F T)
@[expose] def driftVersion (U : PredictableProcessL2 F P) (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  primitive (cutRepresentative U T)
theorem driftVersion_stronglyAdapted (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    StronglyAdapted F (driftVersion U T) :=
  primitive_stronglyAdapted _ (cutRepresentative_stronglyMeasurable U T)
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
theorem cutRepresentative_sub_ae (U V : PredictableProcessL2 F P) (T : ℝ≥0) :
    cutRepresentative (U - V) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun p => cutRepresentative U T p - cutRepresentative V T p) := by
  filter_upwards [representative_ae (U - V), representative_ae U, representative_ae V,
    Lp.coeFn_sub (U : TimeProcessL2 P) (V : TimeProcessL2 P)] with p hsub hU hV hUV
  change representative (U - V) p = ((U : TimeProcessL2 P) - (V : TimeProcessL2 P)) p at hsub
  by_cases hp : p ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame T
  · simpa only [cutRepresentative, indicator_of_mem hp, hsub, hU, hV, Pi.sub_apply] using hUV
  · simp [cutRepresentative, hp]
open SphericalAging.HardSphereDynamics SphericalAging.PredictableItoTime
variable {N : ℕ}
/-- The deterministic operator uses exactly the manuscript's real-time
Lebesgue integral after the canonical nonnegative-time identification. -/
theorem primitive_eq_real_intervalIntegral (H : ℝ≥0 × Ω → ℝ) (t : ℝ≥0) (omega : Ω) :
    primitive H t omega = ∫ s in (0 : ℝ)..(t : ℝ), H (s.toNNReal, omega) := by
  have himage : ((↑) : ℝ≥0 → ℝ) '' Ioc (0 : ℝ≥0) t = Ioc (0 : ℝ) (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
    · intro hx
      exact ⟨⟨x, hx.1.le⟩, ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩, rfl⟩
  have hmap : Measure.map ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) t)) =
        volume.restrict (Ioc (0 : ℝ) (t : ℝ)) := by
    rw [nonnegativeLebesgueMeasure,
      measurableEmbedding_nnrealCoe_iterated.restrict_comap,
      measurableEmbedding_nnrealCoe_iterated.map_comap,
      Measure.restrict_restrict measurableEmbedding_nnrealCoe_iterated.measurableSet_range,
      inter_eq_right.mpr (image_subset_range _ _), himage]
  rw [intervalIntegral.integral_of_le t.coe_nonneg, ← hmap,
    measurableEmbedding_nnrealCoe_iterated.integral_map]
  simp only [Real.toNNReal_coe, primitive]
end SphericalAging.PredictableDriftTime
