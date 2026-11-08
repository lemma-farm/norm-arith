module
/-
Quadratic Gaussian integration helpers adapted from Harry_Xu’s accepted Prove2Me proof:
https://prove2.me/theorems/bea02c80-f5c4-4a04-8431-0ba9ac10fe54
Submission 166b3e3d-2ca5-4b2a-ade4-cdfad74ab4e7.
The copied helpers are proved locally here; no external theorem axiom is assumed.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
set_option autoImplicit false
@[expose] public section
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal
namespace DiscriminativeKalmanFilter.Proof
theorem dot_mulVec_comm_of_isHermitian
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : K j i = K i j := by
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hK.eq
    simpa using heq
  rw [hsym]
  ring
theorem quadratic_completion
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S x : Fin d → ℝ) :
    x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x) =
      1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S) -
        1 / 2 * ((x - K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (x - K⁻¹ *ᵥ S)) := by
  have hunit : IsUnit K := hK.isUnit
  have hdetunit : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hKS : K *ᵥ (K⁻¹ *ᵥ S) = S := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdetunit]
    exact one_mulVec S
  have hcomm (u v : Fin d → ℝ) :
      u ⬝ᵥ K *ᵥ v = v ⬝ᵥ K *ᵥ u :=
    dot_mulVec_comm_of_isHermitian hK.isHermitian u v
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hKS, hcomm (K⁻¹ *ᵥ S) x, hKS,
    dotProduct_comm (K⁻¹ *ᵥ S) S]
  ring
theorem sqrt_mulVec_sq
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (x : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ x =
      (CFC.sqrt K *ᵥ x) ⬝ᵥ (CFC.sqrt K *ᵥ x) := by
  let B := CFC.sqrt K
  have hBps : B.PosSemidef :=
    nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hBB : B * B = K :=
    CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  have hxvec : x ᵥ* B = B *ᵥ x := by
    have heq := vecMul_conjTranspose B x
    rw [hBps.isHermitian.eq] at heq
    simpa [B] using heq
  calc
    x ⬝ᵥ K *ᵥ x = x ⬝ᵥ (B * B) *ᵥ x := by rw [hBB]
    _ = x ⬝ᵥ B *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec]
    _ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by rw [dotProduct_mulVec, hxvec]
theorem isotropic_b_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    fun _ => integrable_exp_neg_mul_sq hb
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod
theorem isotropic_b_integral (d : ℕ) (b : ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (-b * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-b * r ^ 2))]
  rw [show (∫ r : ℝ, Real.exp (-b * r ^ 2)) =
      Real.sqrt (Real.pi / b) by exact integral_gaussian b,
    Finset.prod_const]
  simp
theorem isotropic_integrable (d : ℕ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-1 / 2 * r ^ 2)) :=
    fun _ => by
      simpa only [neg_div] using
        integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod
theorem isotropic_integral (d : ℕ) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-1 / 2 * r ^ 2))]
  have hscalar :
      (∫ r : ℝ, Real.exp (-1 / 2 * r ^ 2)) =
        Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
    simpa only [neg_div] using integral_gaussian (1 / 2 : ℝ)
  rw [hscalar, Finset.prod_const]
  simp
theorem centered_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hmap :
      Measure.map (toLin' B) volume =
        ENNReal.ofReal (abs B.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet
  have hgsmul :
      Integrable (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    rw [hmap]
    exact (isotropic_integrable d).smul_measure (by finiteness)
  have hcomp := hgsmul.comp_measurable hBmeas
  have hfun : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) ∘ (toLin' B) := by
    funext x
    simp only [B, Function.comp_apply, toLin'_apply, sqrt_mulVec_sq hK]
  rw [hfun]
  exact hcomp
theorem centered_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hgsm :
      AEStronglyMeasurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    have hm : Measurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) := by
      simp only [dotProduct]
      fun_prop
    exact hm.aestronglyMeasurable
  have hi := integral_map hBmeas.aemeasurable hgsm
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet,
    integral_smul_measure] at hi
  rw [isotropic_integral d] at hi
  simpa only [B, toLin'_apply, sqrt_mulVec_sq hK, smul_eq_mul] using hi.symm
theorem shifted_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1
    simp only [c]
    ring
  rw [heq]
  exact ((centered_quadratic_integrable hK).comp_sub_right c).const_mul _
theorem shifted_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    (∫ x : Fin d → ℝ,
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
        (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
          (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1
    simp only [c]
    ring
  have htrans :
      (∫ a : Fin d → ℝ,
        Real.exp (-1 / 2 * ((a - c) ⬝ᵥ K *ᵥ (a - c)))) =
      ∫ a : Fin d → ℝ, Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a)) :=
    integral_sub_right_eq_self
      (fun a : Fin d → ℝ => Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a))) c
  rw [heq, integral_const_mul, htrans, centered_quadratic_integral hK]
  ring
end DiscriminativeKalmanFilter.Proof
