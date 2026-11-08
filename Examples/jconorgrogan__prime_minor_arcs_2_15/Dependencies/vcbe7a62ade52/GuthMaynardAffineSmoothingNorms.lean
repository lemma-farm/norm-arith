import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationAffineEnergy
import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationFirstPoissonFourierShift
import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationMediumRegionIntegration
import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationSourceFourierDecay
import Mathlib.Analysis.Fourier.Convolution
open MeasureTheory
open scoped BigOperators Real FourierTransform Convolution
noncomputable section
namespace GuthMaynardJIteration
/-!
# Norm control for the smoothing in Guth--Maynard Proposition 9.1

This file formalizes the two norm comparisons used immediately after applying
Lemma 9.2 in the downward epsilon iteration.  The kernel is the literal source
normalization `T * psi (T * (x-u))` from `affineSmoothing`.
-/
/-- The scaled translate of the smoothing kernel has exactly the same mass as
`psi`.  This is the Jacobian cancellation behind the source normalization. -/
theorem integral_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (x : ℝ) :
    (∫ u : ℝ, T * psi (T * (x - u))) = ∫ z : ℝ, psi z := by
  have hchange := integral_affine_change_real psi (-T) (T * x)
  have habs : |(-T)⁻¹| = T⁻¹ := by
    rw [inv_neg, abs_neg, abs_inv, abs_of_pos hT]
  calc
    (∫ u : ℝ, T * psi (T * (x - u))) =
        T * ∫ u : ℝ, psi (T * x + (-T) * u) := by
      rw [integral_const_mul]
      apply congrArg (fun y : ℝ => T * y)
      apply integral_congr_ae
      filter_upwards with u
      congr 2
      ring
    _ = T * (|(-T)⁻¹| * ∫ z : ℝ, psi z) := by rw [hchange]
    _ = ∫ z : ℝ, psi z := by
      rw [habs]
      field_simp [hT.ne']
/-- The same mass identity with the integration variable in the first slot.
This is the orientation needed after the Fubini swap. -/
theorem integral_affineSmoothing_kernel_right
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (u : ℝ) :
    (∫ x : ℝ, T * psi (T * (x - u))) = ∫ z : ℝ, psi z := by
  have hchange := integral_affine_change_real psi T (-T * u)
  have habs : |T⁻¹| = T⁻¹ := by rw [abs_inv, abs_of_pos hT]
  calc
    (∫ x : ℝ, T * psi (T * (x - u))) =
        T * ∫ x : ℝ, psi (-T * u + T * x) := by
      rw [integral_const_mul]
      apply congrArg (fun y : ℝ => T * y)
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    _ = T * (|T⁻¹| * ∫ z : ℝ, psi z) := by rw [hchange]
    _ = ∫ z : ℝ, psi z := by
      rw [habs]
      field_simp [hT.ne']
/-- Weighted Cauchy--Schwarz in the exact form used for a positive smoothing
kernel. -/
theorem integral_weighted_mul_sq_le
    (k f : ℝ → ℝ)
    (hk0 : ∀ u, 0 ≤ k u)
    (hf0 : ∀ u, 0 ≤ f u)
    (hkmeas : AEStronglyMeasurable k)
    (hfmeas : AEStronglyMeasurable f)
    (hk : Integrable k)
    (hkf2 : Integrable (fun u => k u * f u ^ 2)) :
    (∫ u : ℝ, k u * f u) ^ 2 ≤
      (∫ u : ℝ, k u) * (∫ u : ℝ, k u * f u ^ 2) := by
  let a : ℝ → ℝ := fun u => Real.sqrt (k u)
  let b : ℝ → ℝ := fun u => Real.sqrt (k u) * f u
  have hameas : AEStronglyMeasurable a := by
    exact Real.continuous_sqrt.aestronglyMeasurable.comp_aemeasurable
      hkmeas.aemeasurable
  have hbmeas : AEStronglyMeasurable b := hameas.mul hfmeas
  have ha2 : Integrable (fun u => a u ^ 2) := by
    convert hk using 1
    funext u
    dsimp only [a]
    exact Real.sq_sqrt (hk0 u)
  have hb2 : Integrable (fun u => b u ^ 2) := by
    convert hkf2 using 1
    funext u
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hk0 u)]
  have hcs := integral_mul_sq_le a b hameas hbmeas ha2 hb2
    (fun _ => Real.sqrt_nonneg _)
    (fun u => mul_nonneg (Real.sqrt_nonneg _) (hf0 u))
  have hprod : (fun u => a u * b u) = (fun u => k u * f u) := by
    funext u
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hk0 u)]
  have hka : (fun u => a u ^ 2) = k := by
    funext u
    exact Real.sq_sqrt (hk0 u)
  have hkfb : (fun u => b u ^ 2) = (fun u => k u * f u ^ 2) := by
    funext u
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hk0 u)]
  simpa only [hprod, hka, hkfb] using hcs
/-- Integrability of the scaled smoothing kernel. -/
theorem integrable_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) {psi : ℝ → ℝ} (hpsi : Integrable psi) :
    Integrable (fun y : ℝ => T * psi (T * y)) := by
  exact (hpsi.comp_mul_left' hT.ne').const_mul T
/-- The literal two-variable smoothing integrand is integrable whenever both
one-variable factors are.  This is the Fubini package used by the source. -/
theorem integrable_affineSmoothing_product
    {T : ℝ} (hT : 0 < T) {psi f : ℝ → ℝ}
    (hpsi : Integrable psi) (hf : Integrable f) :
    Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u) (volume.prod volume) := by
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  have hk : Integrable k := integrable_affineSmoothing_kernel hT hpsi
  have hconv := hf.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hk
  simpa only [k, Function.uncurry_def, ContinuousLinearMap.mul_apply', mul_comm] using! hconv
/-- The source smoothing is literally convolution with the scaled kernel. -/
theorem affineSmoothing_eq_convolution
    (T : ℝ) (psi f : ℝ → ℝ) :
    affineSmoothing T psi f = MeasureTheory.convolution f
      (fun y : ℝ => T * psi (T * y))
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  unfold affineSmoothing
  apply integral_congr_ae
  filter_upwards with u
  rw [ContinuousLinearMap.mul_apply']
  ring
/-- The smoothing orbit remains in `L¹`; this is the exact source profile
closure needed before Lemma 9.2 is iterated. -/
theorem integrable_affineSmoothing
    {T : ℝ} (hT : 0 < T) {psi f : ℝ → ℝ}
    (hpsi : Integrable psi) (hf : Integrable f) :
    Integrable (affineSmoothing T psi f) := by
  rw [affineSmoothing_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_affineSmoothing_kernel hT hpsi)
/-- Continuity of the smoothing orbit from an integrable source profile and a
continuous bounded kernel. -/
theorem continuous_affineSmoothing
    {T P : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiBound : ∀ z, ‖psi z‖ ≤ P)
    (hpsiCont : Continuous psi) (hf : Integrable f) :
    Continuous (affineSmoothing T psi f) := by
  rw [affineSmoothing_eq_convolution]
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  have hkCont : Continuous k := by
    exact continuous_const.mul
      (hpsiCont.comp (continuous_const.mul continuous_id))
  have hkbdd : BddAbove (Set.range fun y => ‖k y‖) := by
    refine ⟨T * P, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only [k]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left (hpsiBound (T * y)) hT.le
  exact hkbdd.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) hf hkCont
/-- Complexification commutes with the source smoothing and turns it into the
complex convolution used by the Fourier convolution theorem. -/
theorem ofReal_affineSmoothing_eq_complexConvolution
    (T : ℝ) (psi f : ℝ → ℝ) :
    (fun x : ℝ => (affineSmoothing T psi f x : ℂ)) =
      MeasureTheory.convolution (fun u : ℝ => (f u : ℂ))
        (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  unfold affineSmoothing
  calc
    ((∫ u : ℝ, T * psi (T * (x - u)) * f u : ℝ) : ℂ) =
        ∫ u : ℝ, ((T * psi (T * (x - u)) * f u : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = ∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (f t : ℂ)
          ((T * psi (T * (x - t)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [ContinuousLinearMap.mul_apply']
      push_cast
      ring
/-- The normalized scaled smoothing kernel has Fourier transform
`psiHat(xi/T)` with no residual Jacobian. -/
theorem fourier_scaled_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier
        (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ)) xi =
      FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) := by
  have hfun : (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ)) =
      (fun y : ℝ => (T : ℂ) * (psi (T * y) : ℂ)) := by
    funext y
    push_cast
    rfl
  rw [hfun, source_fourier_const_mul]
  rw [fourier_dilation (fun z : ℝ => (psi z : ℂ)) hT.ne' xi]
  have habs : |T⁻¹| = T⁻¹ := by rw [abs_inv, abs_of_pos hT]
  rw [habs]
  rw [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne']
  norm_num
/-- Exact Fourier multiplier identity for the smoothing orbit used in the
Proposition 9.1 induction. -/
theorem fourier_ofReal_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f) (xi : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ)) xi =
      FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi *
        FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) := by
  let kR : ℝ → ℝ := fun y => T * psi (T * y)
  let fC : ℝ → ℂ := fun u => (f u : ℂ)
  let kC : ℝ → ℂ := fun y => (kR y : ℂ)
  have hkR : Integrable kR := integrable_affineSmoothing_kernel hT hpsi
  have hfC : Integrable fC := hf.ofReal
  have hkC : Integrable kC := hkR.ofReal
  have hfCCont : Continuous fC := Complex.continuous_ofReal.comp hfCont
  have hkRCont : Continuous kR := by
    exact continuous_const.mul
      (hpsiCont.comp (continuous_const.mul continuous_id))
  have hkCCont : Continuous kC := Complex.continuous_ofReal.comp hkRCont
  rw [ofReal_affineSmoothing_eq_complexConvolution]
  rw [Real.fourier_mul_convolution_eq hfC hkC xi]
  change FourierTransform.fourier fC xi * FourierTransform.fourier kC xi = _
  rw [show FourierTransform.fourier kC xi =
      FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) by
    exact fourier_scaled_affineSmoothing_kernel hT psi xi]
/-- A compact support interval for `f` and a radius support for `psi` give the
exact left endpoint of the enlarged smoothing support. -/
theorem affineSmoothing_eq_zero_of_lt_support
    {T a b R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b)
    (hx : x < a - R / T) :
    affineSmoothing T psi f x = 0 := by
  unfold affineSmoothing
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hfu : f u = 0
  · simp [hfu]
  by_cases hpsi : psi (T * (x - u)) = 0
  · simp [hpsi]
  have hker := hpsiSupport (T * (x - u)) hpsi
  have habsT : T * |x - u| ≤ R := by
    simpa only [abs_mul, abs_of_pos hT] using hker
  have habs : |x - u| ≤ R / T := (le_div_iff₀ hT).2 (by
    simpa [mul_comm] using habsT)
  have hu := (hfSupport u hfu).1
  have hleft := neg_le_of_abs_le habs
  exfalso
  linarith
/-- The matching right endpoint of the enlarged smoothing support. -/
theorem affineSmoothing_eq_zero_of_support_lt
    {T a b R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b)
    (hx : b + R / T < x) :
    affineSmoothing T psi f x = 0 := by
  unfold affineSmoothing
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hfu : f u = 0
  · simp [hfu]
  by_cases hpsi : psi (T * (x - u)) = 0
  · simp [hpsi]
  have hker := hpsiSupport (T * (x - u)) hpsi
  have habsT : T * |x - u| ≤ R := by
    simpa only [abs_mul, abs_of_pos hT] using hker
  have habs : |x - u| ≤ R / T := (le_div_iff₀ hT).2 (by
    simpa [mul_comm] using habsT)
  have hu := (hfSupport u hfu).2
  have hright := le_of_abs_le habs
  exfalso
  linarith
/-- Symmetric support form used in the finite affine-range construction. -/
theorem affineSmoothing_abs_support
    {T F R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → |u| ≤ F)
    (hx : affineSmoothing T psi f x ≠ 0) :
    |x| ≤ F + R / T := by
  rw [abs_le]
  constructor
  · by_contra hleft
    apply hx
    apply affineSmoothing_eq_zero_of_lt_support hT psi f hpsiSupport
      (fun u hu => (abs_le.mp (hfSupport u hu)))
    have : x < -(F + R / T) := lt_of_not_ge hleft
    linarith
  · by_contra hright
    apply hx
    apply affineSmoothing_eq_zero_of_support_lt hT psi f hpsiSupport
      (fun u hu => (abs_le.mp (hfSupport u hu)))
    exact lt_of_not_ge hright
/-- Exact `L¹` mass of the smoothing, with the Fubini condition stated on the
literal two-variable kernel. -/
theorem integral_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hprod : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u) (volume.prod volume)) :
    (∫ x : ℝ, affineSmoothing T psi f x) =
      (∫ z : ℝ, psi z) * ∫ u : ℝ, f u := by
  unfold affineSmoothing
  calc
    (∫ x : ℝ, ∫ u : ℝ, T * psi (T * (x - u)) * f u) =
        ∫ u : ℝ, ∫ x : ℝ, T * psi (T * (x - u)) * f u :=
      integral_integral_swap hprod
    _ = ∫ u : ℝ, (∫ z : ℝ, psi z) * f u := by
      apply integral_congr_ae
      filter_upwards with u
      calc
        (∫ x : ℝ, T * psi (T * (x - u)) * f u) =
            (∫ x : ℝ, T * psi (T * (x - u))) * f u := by
          rw [integral_mul_const]
        _ = (∫ z : ℝ, psi z) * f u := by
          rw [integral_affineSmoothing_kernel_right hT psi u]
    _ = (∫ z : ℝ, psi z) * ∫ u : ℝ, f u := by
      rw [integral_const_mul]
/-- Pointwise weighted Cauchy--Schwarz for the literal affine smoothing. -/
theorem affineSmoothing_sq_le_kernelMass_mul
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hfmeas : AEStronglyMeasurable f)
    (x : ℝ)
    (hk : Integrable (fun u : ℝ => T * psi (T * (x - u))))
    (hkf2 : Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2)) :
    affineSmoothing T psi f x ^ 2 ≤
      (∫ z : ℝ, psi z) *
        ∫ u : ℝ, T * psi (T * (x - u)) * f u ^ 2 := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk0 : ∀ u, 0 ≤ k u := fun u =>
    mul_nonneg hT.le (hpsi0 (T * (x - u)))
  have hweighted := integral_weighted_mul_sq_le k f hk0 hf0
    hk.aestronglyMeasurable hfmeas hk hkf2
  unfold affineSmoothing
  rw [integral_affineSmoothing_kernel hT psi x] at hweighted
  exact hweighted
/-- The `L²` contraction used in the Proposition 9.1 iteration.  The stated
integrability hypotheses are precisely the Fubini/Bochner obligations; the
inequality itself has no hidden constant. -/
theorem integral_sq_affineSmoothing_le
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hfmeas : AEStronglyMeasurable f)
    (hkernel : ∀ x, Integrable (fun u : ℝ =>
      T * psi (T * (x - u))))
    (hprodF2 : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) (volume.prod volume))
    (hsmooth2 : Integrable (fun x : ℝ =>
      affineSmoothing T psi f x ^ 2)) :
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
      (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := by
  let mass : ℝ := ∫ z : ℝ, psi z
  let F2 : ℝ → ℝ := fun u => f u ^ 2
  have hmass0 : 0 ≤ mass := integral_nonneg hpsi0
  have hinner : Integrable (fun x : ℝ =>
      ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) := by
    exact hprodF2.integral_prod_left
  have hrhs : Integrable (fun x : ℝ =>
      mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hinner.const_mul mass
  have hkernelF2 : ∀ᵐ x : ℝ, Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) := hprodF2.prod_right_ae
  have hmono :
      (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        ∫ x : ℝ, mass *
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := by
    apply integral_mono_ae hsmooth2 hrhs
    filter_upwards [hkernelF2] with x hx
    simpa only [mass, F2] using
      affineSmoothing_sq_le_kernelMass_mul hT psi f hpsi0 hf0 hfmeas x
        (hkernel x) hx
  have hmassF2 :
      (∫ x : ℝ, ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) =
        mass * ∫ u : ℝ, F2 u := by
    simpa only [mass, F2, affineSmoothing] using
      integral_affineSmoothing hT psi F2 hprodF2
  calc
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        ∫ x : ℝ, mass *
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := hmono
    _ = mass * (∫ x : ℝ,
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) := by
      rw [integral_const_mul]
    _ = mass * (mass * ∫ u : ℝ, F2 u) := by rw [hmassF2]
    _ = (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := by
      dsimp only [mass, F2]
      ring
/-- Ordinary `L¹/L²` integrability of the source and `L¹` integrability of the
positive kernel imply that the squared smoothing itself is integrable. -/
theorem integrable_sq_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hf2 : Integrable (fun u : ℝ => f u ^ 2)) :
    Integrable (fun x : ℝ => affineSmoothing T psi f x ^ 2) := by
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  let mass : ℝ := ∫ z : ℝ, psi z
  let F2 : ℝ → ℝ := fun u => f u ^ 2
  have hk : Integrable k := integrable_affineSmoothing_kernel hT hpsi
  have hkernel : ∀ x, Integrable (fun u : ℝ =>
      T * psi (T * (x - u))) := by
    intro x
    simpa only [k] using hk.comp_sub_left x
  have hprodF2 : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) (volume.prod volume) :=
    integrable_affineSmoothing_product hT hpsi hf2
  have hinner : Integrable (fun x : ℝ =>
      ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hprodF2.integral_prod_left
  have hrhs : Integrable (fun x : ℝ =>
      mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hinner.const_mul mass
  have hkernelF2 : ∀ᵐ x : ℝ, Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) := hprodF2.prod_right_ae
  have hpoint : ∀ᵐ x : ℝ,
      affineSmoothing T psi f x ^ 2 ≤
        mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := by
    filter_upwards [hkernelF2] with x hx
    simpa only [mass, F2] using
      affineSmoothing_sq_le_kernelMass_mul hT psi f hpsi0 hf0
        hf.aestronglyMeasurable x (hkernel x) hx
  have hconv : Integrable (MeasureTheory.convolution f k
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk
  have hsmoothMeas : AEStronglyMeasurable
      (fun x : ℝ => affineSmoothing T psi f x ^ 2) := by
    rw [affineSmoothing_eq_convolution T psi f]
    exact hconv.aestronglyMeasurable.pow 2
  apply hrhs.mono' hsmoothMeas
  filter_upwards [hpoint] with x hx
  have hlhs0 : 0 ≤ affineSmoothing T psi f x ^ 2 := sq_nonneg _
  have hinner0 : 0 ≤ ∫ u : ℝ,
      T * psi (T * (x - u)) * F2 u := by
    apply integral_nonneg
    intro u
    exact mul_nonneg (mul_nonneg hT.le (hpsi0 _)) (sq_nonneg _)
  have hrhs0 : 0 ≤ mass * ∫ u : ℝ,
      T * psi (T * (x - u)) * F2 u :=
    mul_nonneg (integral_nonneg hpsi0) hinner0
  simpa only [Real.norm_eq_abs, abs_of_nonneg hlhs0, abs_of_nonneg hrhs0] using hx
structure SourceAdmissibleProfile
    (T S F : ℝ) (f : ℝ → ℝ) : Prop where
  nonneg : ∀ u, 0 ≤ f u
  bounded : ∀ u, f u ≤ S
  supported : ∀ u, f u ≠ 0 → |u| ≤ F
  integrable : Integrable f
  squareIntegrable : Integrable (fun u => f u ^ 2)
  continuous : Continuous f
  rapidDecay : SourceFourierRapidDecay
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) T S
structure SourceSmoothingKernel (R : ℝ) (psi : ℝ → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ psi z
  bounded : ∀ z, psi z ≤ 1
  supported : ∀ z, psi z ≠ 0 → |z| ≤ R
  integrable : Integrable psi
  continuous : Continuous psi
  mass_le_one : ∫ z : ℝ, psi z ≤ 1
theorem SourceAdmissibleProfile.bound_nonneg
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f) :
    0 ≤ S :=
  (hf.nonneg 0).trans (hf.bounded 0)
end GuthMaynardJIteration
