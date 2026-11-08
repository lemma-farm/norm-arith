module
public import Examples.pmaronow__aging_palomar.Dependencies.v0e468c4ee178.SphericalAging.HardSphereDynamics
public import Examples.pmaronow__aging_palomar.Dependencies.v0e468c4ee178.FourPapersCommon.FilteredItoL2Continuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Examples.pmaronow__aging_palomar.Dependencies.v0e468c4ee178.FourPapersCommon.ContinuousAEAdaptedPredictable
set_option autoImplicit false
public section
/-!
# Finite-driver stochastic integration for the sphere SDE

The driving filtration includes all coordinates. The stochastic operators
below are finite sums of the actual isometrically constructed integrals.
Their continuous versions are proved by the elementary predictable density
and Doob estimates in `FourPapersCommon.FilteredItoContinuous`.
-/
noncomputable section
namespace SphericalAging.HardSphereDynamics
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal BigOperators ContDiff InnerProductSpace RealInnerProductSpace
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
@[expose] abbrev PredictableStateL2 (N : ℕ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) :=
  lpMeas (State N) ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)
theorem lipschitzWith_centered {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) : LipschitzWith K (fun x => g x - g 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hg.dist_le_mul x y
/-- Genuine nonlinear composition on the predictable closed L² space. -/
@[expose] def centeredPredictableCoefficient {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N 𝓕 P) : PredictableProcessL2 𝓕 P :=
  ⟨(lipschitzWith_centered hg).compLp (by simp) (U : Lp (State N) 2
    (nonnegativeLebesgueMeasure.prod P)),
    ((lipschitzWith_centered hg).continuous.comp_aestronglyMeasurable
      (lpMeas.aestronglyMeasurable U)).congr
        ((lipschitzWith_centered hg).coeFn_compLp (by simp)
          (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).symm⟩
theorem norm_centeredPredictableCoefficient_sub_le {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U V : PredictableStateL2 N 𝓕 P) :
    ‖centeredPredictableCoefficient hg U - centeredPredictableCoefficient hg V‖ ≤
      K * ‖U - V‖ :=
  (lipschitzWith_centered hg).norm_compLp_sub_le (by simp)
    (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
/-- Finite-time nonlinear coefficient, including its actual nonzero value
at the zero state. The deterministic term is the elementary predictable
constant on `(0,T]`. -/
@[expose] def predictableCoefficient {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N 𝓕 P) (T : ℝ≥0) :
    PredictableProcessL2 𝓕 P :=
  FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 T
    (centeredPredictableCoefficient hg U) +
    g 0 • elementaryPredictable 𝓕 0 T (adaptedOne (P := P) 𝓕 0)
theorem norm_predictableCoefficient_sub_le {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U V : PredictableStateL2 N 𝓕 P) (T : ℝ≥0) :
    ‖predictableCoefficient hg U T - predictableCoefficient hg V T‖ ≤ K * ‖U - V‖ := by
  simp only [predictableCoefficient, add_sub_add_right_eq_sub,
    ← FourPapersCommon.FilteredBrownian.predictableTimeRestrict_sub]
  exact (FourPapersCommon.FilteredBrownian.norm_predictableTimeRestrict_le 𝓕 T _).trans
    (norm_centeredPredictableCoefficient_sub_le hg U V)
end SphericalAging.HardSphereDynamics
