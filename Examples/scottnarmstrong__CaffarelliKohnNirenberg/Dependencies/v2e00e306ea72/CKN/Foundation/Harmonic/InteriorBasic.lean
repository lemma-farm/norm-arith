-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.NewtonianRepresentation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Pressure.Cutoff
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Pressure.LeibnizLaplacian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.NewtonianKernelIntegrability
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section
namespace CKN.Foundation.Heat
def q (z : Vec3) : ℝ := ∑ i : Fin 3, z i ^ 2
lemma q_pos {z : Vec3} (hz : z ≠ 0) : 0 < q z := by
  have hsum : q z = vec3EuclideanNorm z ^ 2 := by
    unfold q vec3EuclideanNorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  rw [hsum]
  have : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    apply hz
    exact (WithLp.toLp_eq_zero 2).mp hzero
  positivity
lemma q_eq_vec3Norm_sq (z : Vec3) :
    q z = vec3EuclideanNorm z ^ 2 := by
  unfold q vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
private lemma hasFDerivAt_q (z : Vec3) :
    HasFDerivAt q
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
  have hfun : q = ∑ i : Fin 3, (fun y : Vec3 => y i * y i) := by
    funext y
    simp [q, pow_two]
  have hsum : HasFDerivAt
      (∑ i : Fin 3, (fun y : Vec3 => y i * y i))
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
    apply HasFDerivAt.sum
    intro i _hi
    have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i z)
    convert hprod using 1
    ext v
    simp [smul_eq_mul]
    ring_nf
  rw [hfun]
  exact hsum
lemma hasFDerivAt_newtonianKernel {z : Vec3} (hz : z ≠ 0) :
    HasFDerivAt newtonianKernel
      ((4 * Real.pi)⁻¹ •
        ((-(1 : ℝ) / 2 * q z ^ (-(1 : ℝ) / 2 - 1)) •
          ∑ i : Fin 3, (2 * z i) •
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
  have hq : HasFDerivAt (fun y : Vec3 => q y ^ (-(1 : ℝ) / 2))
      ((-(1 : ℝ) / 2 * q z ^ (-(1 : ℝ) / 2 - 1)) •
        ∑ i : Fin 3, (2 * z i) •
          (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
    exact (hasFDerivAt_q z).rpow_const (p := -(1 : ℝ) / 2)
      (Or.inl (q_pos hz).ne')
  have hkernel : (fun y : Vec3 => newtonianKernel y) =
      (fun y : Vec3 => (4 * Real.pi)⁻¹ * q y ^ (-(1 : ℝ) / 2)) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp [newtonianKernel, q, vec3EuclideanNorm]
    · rw [newtonianKernel, q_eq_vec3Norm_sq]
      rw [one_div]
      rw [show (4 * Real.pi * vec3EuclideanNorm y)⁻¹ =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm y)⁻¹ by ring]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (sq_nonneg (vec3EuclideanNorm y))]
      have hsqrt : (vec3EuclideanNorm y ^ 2) ^ (1 / 2 : ℝ) =
          vec3EuclideanNorm y := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      rw [hsqrt]
  change HasFDerivAt (fun y : Vec3 => newtonianKernel y) _ z
  rw [hkernel]
  exact hq.const_mul (4 * Real.pi)⁻¹
lemma spatialDeriv_newtonianKernel_shift {x y : Vec3} (hxy : x - y ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) i y =
      (4 * Real.pi)⁻¹ * (x - y) i * q (x - y) ^ (-(3 : ℝ) / 2) := by
  have hsub : HasFDerivAt (fun z : Vec3 => x - z)
      (-ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hcomp := (hasFDerivAt_newtonianKernel hxy).comp y hsub
  have hi := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hcomp.fderiv
  change (fderiv ℝ (newtonianKernel ∘ (fun z : Vec3 => x - z)) y)
      (CKN.basisVec i) = _
  rw [hi]
  simp only [ContinuousLinearMap.comp_apply]
  simp [smul_eq_mul, CKN.basisVec_apply]
  ring_nf
def eta (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) : Vec3 → ℝ :=
  mollifiedBallCutoff x₀ hρ
/-- The Newtonian kernel times one cutoff derivative. -/
def kernelCutoffDerivative (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) (y : Vec3) : ℝ :=
  newtonianKernel (x - y) * spatialDeriv (eta x₀ hρ) i y
lemma contDiff_spatialDeriv_two {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv f i) := by
  have hfd := hf.contDiff_fderiv_apply (m := (2 : ℕ))
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hc : ContDiff ℝ (2 : ℕ)
      (fun x : Vec3 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hfd.comp hc
  change ContDiff ℝ (2 : ℕ)
    (fun x : Vec3 => (fderiv ℝ f x) (basisVec i))
  exact hcomp
theorem newtonianKernel_size_bound {z : Vec3} (hz : z ≠ 0) :
    |newtonianKernel z| ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrn : 0 < vec3EuclideanNorm z :=
    lt_of_lt_of_le hzn (CKN.space_norm_le_euclideanNorm z)
  have hinv : (vec3EuclideanNorm z)⁻¹ ≤ ‖z‖⁻¹ := by
    exact (inv_le_inv₀ hrn hzn).2 (CKN.space_norm_le_euclideanNorm z)
  rw [newtonianKernel, abs_of_nonneg (by positivity)]
  rw [show 1 / (4 * Real.pi * vec3EuclideanNorm z) =
      (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z)⁻¹ by field_simp]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)
end CKN.Foundation.Heat
