module
public import DiscriminativeKalmanFilter.Proof.DensityTools
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DiscriminativeKalmanFilter.Proof

variable {d : ℕ}

theorem gaussianPDF_pos (m : State d) {C : Covariance d} (hC : C.PosDef)
    (z : State d) : 0 < gaussianPDF m C z := by
  unfold gaussianPDF
  have : 0 < (2 * Real.pi) ^ d * C.det :=
    mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) _) hC.det_pos
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr this)) (Real.exp_pos _)

theorem gaussianPDF_continuous (m : State d) (C : Covariance d) :
    Continuous (gaussianPDF m C) := by
  unfold gaussianPDF dotProduct mulVec
  fun_prop

theorem gaussianPDF_le (m : State d) {C : Covariance d} (hC : C.PosDef)
    (z : State d) : gaussianPDF m C z ≤ gaussianPDF 0 C 0 := by
  have hq : 0 ≤ (z - m) ⬝ᵥ (C⁻¹ *ᵥ (z - m)) := by
    simpa using hC.posSemidef.inv.dotProduct_mulVec_nonneg (z - m)
  simp only [gaussianPDF, sub_self, mulVec_zero, dotProduct_zero, neg_zero, zero_div,
    Real.exp_zero, mul_one]
  apply mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (by norm_num))

def gaussianBCF (m : State d) {C : Covariance d} (hC : C.PosDef) :
    BoundedContinuousFunction (State d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gaussianPDF m C)
    (gaussianPDF_continuous m C) (gaussianPDF 0 C 0) (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (gaussianPDF_pos m hC z)]
      exact gaussianPDF_le m hC z)

theorem transition_pos (M : Model d) (y z : State d) : 0 < transition M y z :=
  gaussianPDF_pos _ M.Γ_posDef z

theorem transition_le (M : Model d) (y z : State d) :
    transition M y z ≤ gaussianPDF 0 M.Γ 0 :=
  gaussianPDF_le _ M.Γ_posDef z

theorem transition_continuous (M : Model d) :
    Continuous (fun yz : State d × State d => transition M yz.1 yz.2) := by
  unfold transition gaussianPDF dotProduct mulVec
  fun_prop

                                                                                         
                                          
                                                 
                                                                                            

end DiscriminativeKalmanFilter.Proof
