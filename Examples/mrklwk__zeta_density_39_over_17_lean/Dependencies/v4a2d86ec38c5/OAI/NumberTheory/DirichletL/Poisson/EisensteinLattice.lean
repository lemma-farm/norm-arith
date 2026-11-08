module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
namespace EisensteinSchwartzPoisson
section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
def translateSchwartz (f : 𝓢(ℂ, ℂ)) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : ℂ => z + b)
    (by fun_prop) (isometry_add_right b).antilipschitzWith f
def affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (translateSchwartz f b)
@[simp] theorem affinePullback_apply (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b z : ℂ) :
    affinePullback f A b z = f (A z + b) := rfl
end
section
open scoped RealInnerProductSpace
def basisMap (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    w • (Complex.ofRealCLM.comp Complex.imCLM)
@[simp] theorem basisMap_apply (w z : ℂ) :
    basisMap w z = (z.re : ℂ) + w * (z.im : ℂ) := rfl
def basisEquiv (w : ℂ) (hw : w.im ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toLinearMap := (basisMap w).toLinearMap
      invFun z := complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im)
      left_inv z := by
        change complexPoint ((basisMap w z).re - (basisMap w z).im * w.re / w.im)
          ((basisMap w z).im / w.im) = z
        apply Complex.ext
        · simp only [basisMap_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.add_im, Complex.mul_im,  zero_add, complexPoint]
          field_simp [hw]
          ring
        · simp [basisMap_apply, complexPoint, hw]
      right_inv z := by
        change basisMap w (complexPoint (z.re - z.im * w.re / w.im)
          (z.im / w.im)) = z
        apply Complex.ext
        · simp only [basisMap_apply, complexPoint, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
          field_simp [hw]
          ring
        · simp only [basisMap_apply, complexPoint, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add]
          field_simp [hw] }
  continuous_toFun := (basisMap w).continuous
  continuous_invFun := by
    simp only [complexPoint_eq]
    fun_prop
def complexMulEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 c hc)
@[simp] theorem complexMulEquiv_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    complexMulEquiv c hc z = c * z := rfl
def scaledBasisEquiv (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (basisEquiv w hw).trans (complexMulEquiv c hc)
@[simp] theorem scaledBasisEquiv_apply (w : ℂ) (hw : w.im ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    scaledBasisEquiv w hw c hc z = c * ((z.re : ℂ) + w * (z.im : ℂ)) := rfl
end
section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
abbrev O := ActualEisensteinCubic.O
def eisensteinLatticeMap (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  scaledBasisEquiv omega3 omega3_im_ne_zero c hc
theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]
theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair
theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero
end
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
def radialTest (W : 𝓢(ℝ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩ W
@[simp] theorem radialTest_apply (W : 𝓢(ℝ, ℂ)) (z : ℂ) :
    radialTest W z = W (‖z‖ ^ 2) := rfl
end EisensteinSchwartzPoisson
open scoped BigOperators Classical
namespace IdealGaussCRT
end IdealGaussCRT
end
end OAI
