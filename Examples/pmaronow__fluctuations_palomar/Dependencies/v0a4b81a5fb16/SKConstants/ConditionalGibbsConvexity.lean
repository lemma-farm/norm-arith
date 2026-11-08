module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GibbsVariational
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GaussianLebesgueDensity
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.SKGibbsGauge
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GaussianGibbsInterpolation
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal ContDiff
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
def conditionalGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ‖z‖ ^ 2 / 2 - beta * goeSpinHamiltonian sigma x z +
    Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))
def conditionalGibbsSpinMass {n : ℕ} (beta sigma : ℝ) (x : Spin n) : ℝ :=
  ∫ z, gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x
    ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)
def conditionalGibbsGaussianLaw {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    Measure (EuclideanSpace ℝ (Fin n × Fin n)) :=
  (GaussianProposal.primitiveGaussian (Fin n × Fin n)).withDensity
    (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x))
theorem conditionalGibbsSpinMass_pos {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    0 < conditionalGibbsSpinMass beta sigma x := by
  unfold conditionalGibbsSpinMass
  rw [integral_pos_iff_support_of_nonneg
    (fun z => (gibbsProbability_pos beta _ x).le)
    (goeGibbsProbability_integrable beta sigma x)]
  have hs : Function.support
      (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x) = univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gibbsProbability_pos beta _ x).ne'
  rw [hs, measure_univ]
  norm_num
instance conditionalGibbsGaussianLaw_isProbability {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    IsProbabilityMeasure (conditionalGibbsGaussianLaw beta sigma x) := by
  constructor
  rw [conditionalGibbsGaussianLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, ← conditionalGibbsSpinMass,
      div_self (conditionalGibbsSpinMass_pos beta sigma x).ne']
    simp
  · exact (goeGibbsProbability_integrable beta sigma x).div_const _
  · exact ae_of_all _ (fun z => div_nonneg
      (gibbsProbability_pos beta _ x).le (conditionalGibbsSpinMass_pos beta sigma x).le)
theorem conditionalGibbsGaussianLaw_eq_exp_potential {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    conditionalGibbsGaussianLaw beta sigma x =
      volume.withDensity (fun z => ENNReal.ofReal
        (((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
          conditionalGibbsSpinMass beta sigma x) *
          Real.exp (-conditionalGibbsPotential beta sigma x z))) := by
  have hd : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      ENNReal.ofReal (standardGaussianEuclideanDensity z)) := by
    unfold standardGaussianEuclideanDensity
    exact (Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (by fun_prop))).ennreal_ofReal
  have hw : Measurable (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x)) :=
    (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).div_const _).measurable.ennreal_ofReal
  rw [conditionalGibbsGaussianLaw, GaussianProposal.primitiveGaussian,
    stdGaussian_euclidean_eq_withDensity, ← withDensity_mul volume hd hw]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by
      unfold standardGaussianEuclideanDensity
      exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))]
    congr 1
    have he : Real.exp (-conditionalGibbsPotential beta sigma x z) =
        Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (beta * goeSpinHamiltonian sigma x z) /
          gibbsPartition beta (GaussianProposal.goeMatrix sigma z) := by
      unfold conditionalGibbsPotential
      rw [show -(‖z‖ ^ 2 / 2 - beta * goeSpinHamiltonian sigma x z +
        Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))) =
        -‖z‖ ^ 2 / 2 + beta * goeSpinHamiltonian sigma x z -
        Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z)) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_log (gibbsPartition_pos beta _)]
    rw [standardGaussianEuclideanDensity_eq_norm, he]
    unfold gibbsProbability goeSpinHamiltonian
    ring)
end SKConstants
