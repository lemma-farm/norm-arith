module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Mellin.CompactWeights
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def quadraticRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 3
theorem quadraticRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    quadraticRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 3) z := by
  simp only [quadraticRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]
def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖eisEmbedding z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖eisEmbedding z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖eisEmbedding z‖ ^ 2 / M) ^ 2 * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh
theorem quadraticRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    ‖quadraticRow P hg S z‖ ≤ 1 := by
  rw [quadraticRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _
theorem quadratic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
theorem quadratic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (quadratic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
end QuadraticInitialBound
namespace CubicReflectionKernel
end CubicReflectionKernel
end
end OAI
