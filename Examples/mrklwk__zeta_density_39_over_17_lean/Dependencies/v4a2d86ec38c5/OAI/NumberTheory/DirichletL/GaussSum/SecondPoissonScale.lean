module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
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
namespace ActualEisensteinCubic
section
open scoped ComplexConjugate
end
end ActualEisensteinCubic
namespace ConcretePrimeRowBridge
section
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical
end
open ActualEisensteinCubic
end ConcretePrimeRowBridge
namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
def complexPoint (x y : ℝ) : ℂ := ⟨x, y⟩
theorem complexPoint_eq (x y : ℝ) : complexPoint x y = (x : ℂ) + Complex.I * (y : ℂ) := by
  apply Complex.ext <;> simp [complexPoint]
theorem summable_int_cauchy_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  classical
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ℤ))]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (hp.subtype (fun n : ℤ => n ∉ ({0} : Finset ℤ)))
  intro n
  have hn : n.val ≠ 0 := by simpa only [Finset.mem_singleton] using n.property
  have hnr : (n.val : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsq : 0 < (n.val : ℝ) ^ 2 := sq_pos_of_ne_zero hnr
  change (1 + (n.val : ℝ) ^ 2)⁻¹ ≤ 1 / (n.val : ℝ) ^ 2
  simpa only [one_div] using
    one_div_le_one_div_of_le hsq (show (n.val : ℝ) ^ 2 ≤ 1 + (n.val : ℝ) ^ 2 by linarith)
theorem summable_int_cauchy_product :
    Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) :=
  summable_int_cauchy_weight.mul_of_nonneg summable_int_cauchy_weight
    (fun _ => by positivity) (fun _ => by positivity)
theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)
def planeDecayConstant (F : SchwartzMap ℂ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 F + SchwartzMap.seminorm ℝ 2 0 F +
    SchwartzMap.seminorm ℝ 4 0 F
theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith
theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]
end EisensteinSchwartzPoisson
end
end OAI
