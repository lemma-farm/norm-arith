-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
abbrev GaussianMatrix (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℝ ι)
def transposeGaussianMatrix : GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι where
  toFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  invFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm
def symmetrizeGaussianMatrix (s : ℝ) (A : GaussianMatrix ι) : GaussianMatrix ι :=
  s • (A + transposeGaussianMatrix A)
lemma symmetrizeGaussianMatrix_continuous (s : ℝ) :
    Continuous (symmetrizeGaussianMatrix (ι := ι) s) := by
  unfold symmetrizeGaussianMatrix
  fun_prop
def goeLaw (ι : Type*) [Fintype ι] (s : ℝ) : Measure (GaussianMatrix ι) :=
  (stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)
variable [LinearOrder ι]
abbrev UpperEntry (ι : Type*) [LinearOrder ι] := {p : ι × ι // p.1 ≤ p.2}
end
section
open scoped NNReal
section Upper
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
end Upper
def goeUpperMarginal {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) : Measure ℝ :=
  gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)
instance goeUpperMarginal_probability {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) :
    IsProbabilityMeasure (goeUpperMarginal s p) := by
  unfold goeUpperMarginal
  infer_instance
open scoped BigOperators
def borderMatrix {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : GaussianMatrix (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cases (WithLp.toLp 2 (Fin.cases a v))
    (fun i => WithLp.toLp 2 (Fin.cases (v i) (B i))))
@[simp] lemma borderMatrix_zero_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : borderMatrix a v B 0 0 = a := rfl
@[simp] lemma borderMatrix_zero_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B 0 i.succ = v i := rfl
@[simp] lemma borderMatrix_succ_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B i.succ 0 = v i := rfl
@[simp] lemma borderMatrix_succ_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i j : Fin n) : borderMatrix a v B i.succ j.succ = B i j := rfl
instance goeLaw_probability {ι : Type*} [Fintype ι] (s : ℝ) :
    IsProbabilityMeasure (goeLaw ι s) :=
  (Measure.isProbabilityMeasure_map_iff
    (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
end
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
end
open scoped BigOperators
def firstAxis (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i.val = 0 then 1 else 0)
lemma borderMatrix_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
      borderMatrix p.1 p.2.1 p.2.2) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
    borderMatrix p.1 p.2.1 p.2.2 i j)
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ]
  all_goals fun_prop
def columnNormLaw (n : ℕ) (s : ℝ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal).map
    (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)
def assembleTri (n : ℕ) (p : ℝ × (ℝ × GaussianMatrix (Fin n))) : GaussianMatrix (Fin (n+1)) :=
  borderMatrix p.1 (p.2.1 • firstAxis n) p.2.2
lemma assembleTri_measurable (n : ℕ) : Measurable (assembleTri n) :=
  (borderMatrix_measurable n).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd |>.smul measurable_const).prodMk
      (measurable_snd.comp measurable_snd)))
def triMatrixLaw : (n : ℕ) → ℝ → Measure (GaussianMatrix (Fin n))
  | 0, s => goeLaw (Fin 0) s
  | n+1, s => ((gaussianReal 0 (4*s^2).toNNReal).prod
      ((columnNormLaw n s).prod (triMatrixLaw n s))).map (assembleTri n)
lemma columnNorm_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)
      (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal) (columnNormLaw n s) :=
  ⟨(WithLp.measurable_toLp _ _).norm, rfl⟩
instance columnNormLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (columnNormLaw n s) :=
  (Measure.isProbabilityMeasure_map_iff
    (columnNorm_preserving n s).measurable.aemeasurable).2 inferInstance
instance triMatrixLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triMatrixLaw n s) := by
  induction n with
  | zero => exact goeLaw_probability s
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (assembleTri_measurable n).aemeasurable).2 inferInstance
end CriticalSK
end
end OAI
