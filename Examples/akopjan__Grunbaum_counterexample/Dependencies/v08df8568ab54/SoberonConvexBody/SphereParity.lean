import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.SphereMeasure
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.TensorParity
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.Walsh4
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Integrating finite parity extraction

All averages in this file are literal sums over the sixteen coordinate sign
changes. Their integral preservation follows from sphere measure preservation.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 0
instance sphereVolume_finite : IsFiniteMeasure sphereVolume :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure V).toSphere))
/-- The sign convention agrees with the closed positive halfspace in Cells. -/
def closedSign (x : Real) : Real := if 0 <= x then 1 else -1
@[simp] theorem abs_closedSign (x : Real) : abs (closedSign x) = 1 := by
  unfold closedSign
  split <;> norm_num
theorem closedSign_neg (x : Real) (hx : x ≠ 0) :
    closedSign (-x) = -closedSign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hp : 0 <= -x := le_of_lt (neg_pos.mpr h)
    have hn : ¬ 0 <= x := not_le_of_gt h
    simp [closedSign, hp, hn]
  · have hp : 0 <= x := le_of_lt h
    have hn : ¬ 0 <= -x := by linarith
    simp [closedSign, hp, hn]
theorem closedSign_mul_self (x : Real) : closedSign x * x = abs x := by
  by_cases hx : 0 <= x
  · simp [closedSign, hx, abs_of_nonneg hx]
  · simp [closedSign, hx, abs_of_neg (lt_of_not_ge hx)]
theorem closedSign_pos_mul (r x : Real) (hr : 0 < r) :
    closedSign (r * x) = closedSign x := by
  have hiff : 0 <= r * x <-> 0 <= x := by
    constructor
    · intro h
      by_contra hn
      have hx : x < 0 := lt_of_not_ge hn
      have := mul_neg_of_pos_of_neg hr hx
      linarith
    · exact mul_nonneg (le_of_lt hr)
  simp [closedSign, hiff]
/-- Product of the four ambient coordinate signs selected by I. -/
def coordinateCharacter (I : Finset (Fin 4)) (u : UnitSphere) : Real :=
  ∏ i ∈ I, closedSign ((u : V) i)
@[simp] theorem abs_coordinateCharacter (I : Finset (Fin 4)) (u : UnitSphere) :
    abs (coordinateCharacter I u) = 1 := by
  simp [coordinateCharacter, Finset.abs_prod]
theorem measurable_coordinateCharacter (I : Finset (Fin 4)) :
    Measurable (coordinateCharacter I) := by
  unfold coordinateCharacter closedSign
  apply Finset.measurable_prod
  intro i _
  apply Measurable.ite
  · exact measurableSet_le measurable_const (Continuous.measurable (by fun_prop))
  · exact measurable_const
  · exact measurable_const
theorem integrable_coordinateCharacter (I : Finset (Fin 4)) :
    Integrable (coordinateCharacter I) sphereVolume := by
  apply (integrable_const (1 : Real)).mono'
  · exact (measurable_coordinateCharacter I).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      simp only [Real.norm_eq_abs, abs_coordinateCharacter, le_refl])
theorem integrable_continuous_sphere {f : UnitSphere -> Real}
    (hf : Continuous f) : Integrable f sphereVolume := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (hf.continuousOn.integrableOn_compact (μ := sphereVolume) isCompact_univ)
/-- Bounded measurable signs can multiply any continuous sphere function. -/
theorem integrable_sign_mul_continuous
    (s f : UnitSphere -> Real) (hs : Measurable s)
    (habs : forall u, abs (s u) = 1) (hf : Continuous f) :
    Integrable (fun u => s u * f u) sphereVolume := by
  apply (integrable_continuous_sphere hf).norm.mono'
  · exact (hs.mul hf.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      simp only [Real.norm_eq_abs, abs_mul, habs, one_mul, le_refl])
def signFactor (b : Bool) : Real := if b then 1 else -1
abbrev SignQuad := Bool × Bool × Bool × Bool
def quadPattern (s : SignQuad) : Fin 4 -> Bool :=
  ![s.1, s.2.1, s.2.2.1, s.2.2.2]
/-- Diagonal orthogonal transformation associated with four Boolean signs. -/
def signChange (s : SignQuad) : V ≃ₗᵢ[Real] V where
  toFun x := WithLp.toLp 2 (fun i => signFactor (quadPattern s i) * x i)
  invFun x := WithLp.toLp 2 (fun i => signFactor (quadPattern s i) * x i)
  left_inv := by
    intro x
    ext i
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]
  right_inv := by
    intro x
    ext i
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]
  map_add' := by
    intro x y
    ext i
    simp [PiLp.toLp_apply, mul_add]
  map_smul' := by
    intro a x
    ext i
    simp [PiLp.toLp_apply, mul_left_comm]
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]
@[simp] theorem signChange_apply (s : SignQuad) (x : V) (i : Fin 4) :
    signChange s x i = signFactor (quadPattern s i) * x i := rfl
/-- Real character of the finite diagonal sign-change group. -/
def cubeCharacter (I : Finset (Fin 4)) (s : SignQuad) : Real :=
  ∏ i ∈ I, signFactor (quadPattern s i)
private def cubeCharacterZ (I : Finset (Fin 4)) (s : SignQuad) : Int :=
  ∏ i ∈ I, if quadPattern s i then 1 else -1
private theorem cubeCharacter_cast (I : Finset (Fin 4)) (s : SignQuad) :
    (cubeCharacterZ I s : Real) = cubeCharacter I s := by
  simp [cubeCharacterZ, cubeCharacter, signFactor]
set_option maxRecDepth 200000 in
private theorem sum_cubeCharacterZ_nonempty :
    forall I : Finset (Fin 4), I.Nonempty ->
      (∑ s : SignQuad, cubeCharacterZ I s) = 0 := by
  decide
theorem sum_cubeCharacter_nonempty (I : Finset (Fin 4)) (hI : I.Nonempty) :
    (∑ s : SignQuad, cubeCharacter I s) = 0 := by
  have h := sum_cubeCharacterZ_nonempty I hI
  have hh : ((∑ s : SignQuad, cubeCharacterZ I s) : Real) = 0 := by
    exact_mod_cast h
  simpa only [Int.cast_sum, cubeCharacter_cast] using hh
private theorem closedSign_signFactor (b : Bool) (x : Real) (hx : x ≠ 0) :
    closedSign (signFactor b * x) = signFactor b * closedSign x := by
  cases b
  · simpa [signFactor] using closedSign_neg x hx
  · simp [signFactor]
theorem coordinateCharacter_signChange
    (I : Finset (Fin 4)) (s : SignQuad) (u : UnitSphere)
    (hu : forall i : Fin 4, (u : V) i ≠ 0) :
    coordinateCharacter I (sphereMap (signChange s) u) =
      cubeCharacter I s * coordinateCharacter I u := by
  unfold coordinateCharacter cubeCharacter
  simp only [sphereMap_coe, signChange_apply]
  simp_rw [closedSign_signFactor _ _ (hu _)]
  rw [Finset.prod_mul_distrib]
/-- Literal finite average over the sixteen orthogonal sign changes. -/
def cubeAverage (f : UnitSphere -> Real) (u : UnitSphere) : Real :=
  (1 / 16 : Real) * ∑ s : SignQuad, f (sphereMap (signChange s) u)
theorem integral_cubeAverage (f : UnitSphere -> Real)
    (hf : Integrable f sphereVolume) :
    (∫ u, cubeAverage f u ∂ sphereVolume) =
      ∫ u, f u ∂ sphereVolume := by
  have hfs (s : SignQuad) :
      Integrable (fun u => f (sphereMap (signChange s) u)) sphereVolume :=
    (sphereMap_measurePreserving (signChange s)).integrable_comp_of_integrable hf
  unfold cubeAverage
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun s _ => hfs s)]
  simp_rw [integral_comp_sphereMap]
  norm_num [SignQuad] <;> ring
/-- The finite average of a nontrivial coordinate character vanishes. -/
theorem integral_coordinateCharacter_eq_zero
    (I : Finset (Fin 4)) (hI : I.Nonempty) :
    (∫ u, coordinateCharacter I u ∂ sphereVolume) = 0 := by
  have havg : cubeAverage (coordinateCharacter I) =ᵐ[sphereVolume] (fun _ => 0) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    unfold cubeAverage
    simp_rw [coordinateCharacter_signChange I _ u hu]
    rw [← Finset.sum_mul, sum_cubeCharacter_nonempty I hI]
    ring
  rw [← integral_cubeAverage _ (integrable_coordinateCharacter I)]
  calc
    (∫ u, cubeAverage (coordinateCharacter I) u ∂ sphereVolume) =
        ∫ _u : UnitSphere, (0 : Real) ∂ sphereVolume := integral_congr_ae havg
    _ = 0 := by simp
/-- The character times the matching multilinear monomial is nonnegative. -/
theorem character_mul_coordinates (I : Finset (Fin 4)) (u : UnitSphere) :
    coordinateCharacter I u * (∏ i ∈ I, (u : V) i) =
      absCoordinateProduct I u := by
  unfold coordinateCharacter absCoordinateProduct
  rw [← Finset.prod_mul_distrib]
  simp_rw [closedSign_mul_self]
end SoberonConvexBody.SphereGeometry
