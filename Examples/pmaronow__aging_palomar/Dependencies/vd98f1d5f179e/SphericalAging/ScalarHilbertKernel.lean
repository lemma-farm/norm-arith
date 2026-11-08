module
public import Mathlib
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.HilbertSumTensor
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.CKSpecification
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
set_option autoImplicit false
public section
/-! Actual Hilbert feature construction for a scalar positive kernel, using
Mathlib's proved Moore construction. Finite Gram positivity is converted to
the operator-kernel positivity required by that construction. -/
noncomputable section
open scoped InnerProductSpace NNReal TensorProduct
open Set MeasureTheory Filter UniformSpace
namespace SphericalAging.ScalarHilbertKernel
structure PositiveKernel (X : Type) where
  value : X → X → ℝ
  symmetric : ∀ x y, value x y = value y x
  finite_positive : ∀ (n : ℕ) (x : Fin n → X) (a : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, a i * a j * value (x i) (x j)
@[expose] def operatorKernel {X : Type} (K : PositiveKernel X) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  fun x y => K.value x y • ContinuousLinearMap.id ℝ ℝ
theorem finite_positive_fintype {X I : Type} (K : PositiveKernel X)
    [Fintype I] (x : I → X) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * K.value (x i) (x j) := by
  let e := (Fintype.equivFin I).symm
  have hp := K.finite_positive (Fintype.card I) (fun i => x (e i)) (fun i => a (e i))
  have heq : (∑ i, ∑ j, a (e i)*a (e j)*K.value (x (e i)) (x (e j))) =
      ∑ i, ∑ j, a i*a j*K.value (x i) (x j) := by
    calc
      _ = ∑ i, ∑ j : I, a (e i)*a j*K.value (x (e i)) (x j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => a (e i)*a j*K.value (x (e i)) (x j))
      _ = _ := e.sum_comp (fun i => ∑ j : I, a i*a j*K.value (x i) (x j))
  rwa [heq] at hp
theorem finite_positive_finset {X : Type} (K : PositiveKernel X)
    (s : Finset X) (a : X → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i*a j*K.value i j := by
  have hp := finite_positive_fintype K (fun i : s => (i : X)) (fun i => a i)
  have heq : (∑ i : s, ∑ j : s, a i*a j*K.value i j) =
      ∑ i ∈ s, ∑ j ∈ s, a i*a j*K.value i j := by
    calc
      _ = ∑ i : s, ∑ j ∈ s, a i*a j*K.value i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort s (fun j => a i*a j*K.value i j)
      _ = _ := Finset.sum_coe_sort s (fun i => ∑ j ∈ s, a i*a j*K.value i j)
  rwa [heq] at hp
theorem operatorKernel_posSemidef {X : Type} (K : PositiveKernel X) :
    (operatorKernel K).PosSemidef := by
  classical
  apply RKHS.posSemidef_iff_re_sum_kernel'.mpr
  refine ⟨?_, ?_⟩
  · ext x y
    simp [Matrix.conjTranspose_apply, operatorKernel, star_smul, K.symmetric,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
  · intro a
    have hp := finite_positive_finset K a.support a
    simp only [Finsupp.sum, operatorKernel, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, RCLike.inner_apply, RCLike.re_to_real]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [K.symmetric j i]
    simp [mul_comm, mul_left_comm]
instance {X : Type} (K : PositiveKernel X) : Fact (operatorKernel K).PosSemidef :=
  ⟨operatorKernel_posSemidef K⟩
@[expose] abbrev Space {X : Type} (K : PositiveKernel X) := RKHS.OfKernel (operatorKernel K)
end SphericalAging.ScalarHilbertKernel
