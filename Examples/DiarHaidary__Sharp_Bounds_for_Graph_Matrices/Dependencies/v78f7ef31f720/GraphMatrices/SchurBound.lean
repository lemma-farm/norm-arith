import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.v78f7ef31f720.GraphMatrices.SpectralNorm
/-! The rectangular Schur bound for the actual Euclidean operator norm. -/
namespace GraphMatrices
noncomputable section
open scoped BigOperators
private theorem weighted_sum_sq_le
    {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i => Real.sqrt (w i))
    (g := fun i => Real.sqrt (w i) * f i)
  have hprod (i : ι) : Real.sqrt (w i) * (Real.sqrt (w i) * f i) = w i * f i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  simp only [hprod, mul_pow, Real.sq_sqrt (hw _)] at h
  exact h
theorem spectralNorm_schur
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrows : ∀ i, ∑ j, |A i j| ≤ R)
    (hcols : ∀ j, ∑ i, |A i j| ≤ C) :
    spectralNorm A ≤ Real.sqrt (R * C) := by
  classical
  apply (euclideanOperator A).opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  have hrow (i : m) :
      (∑ j, A i j * x j) ^ 2 ≤ R * ∑ j, |A i j| * (x j) ^ 2 := by
    have habs :
        |∑ j, A i j * x j| ≤ ∑ j, |A i j| * |x j| := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun j => A i j * x j) Finset.univ)
    have hsum : 0 ≤ ∑ j, |A i j| * |x j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcs := weighted_sum_sq_le (fun j => |A i j|) (fun j => |x j|)
      (fun j => abs_nonneg _)
    simp only [sq_abs] at hcs
    calc
      (∑ j, A i j * x j) ^ 2 = |∑ j, A i j * x j| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ j, |A i j| * |x j|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ ≤ (∑ j, |A i j|) * ∑ j, |A i j| * (x j) ^ 2 := hcs
      _ ≤ R * ∑ j, |A i j| * (x j) ^ 2 :=
        mul_le_mul_of_nonneg_right (hrows i)
          (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  have hsum :
      (∑ i : m, (∑ j, A i j * x j) ^ 2) ≤ R * C * ∑ j, (x j) ^ 2 := by
    calc
      _ ≤ ∑ i : m, R * ∑ j, |A i j| * (x j) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hrow i)
      _ = R * ∑ j, (∑ i : m, |A i j|) * (x j) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ ≤ R * ∑ j, C * (x j) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hR
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hcols j) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hsq :
      ‖euclideanOperator A x‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [euclideanOperator_apply, Real.norm_eq_abs, sq_abs] using hsum
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq
end
end GraphMatrices
