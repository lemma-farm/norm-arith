module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
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
namespace EisensteinSchwartzPoisson
section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
end
section
open MeasureTheory
open scoped SchwartzMap ContDiff
end
open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap
theorem inverse_square_le_cauchy_product (a b q : ℝ) (hq : 0 ≤ q)
    (hQ : (a ^ 2 + b ^ 2) / 2 ≤ q) :
    ((1 + q) ^ 2)⁻¹ ≤
      4 * ((1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) := by
  have hsum : 1 + a ^ 2 + b ^ 2 ≤ 2 * (1 + q) := by linarith
  have hsquare : (1 + a ^ 2 + b ^ 2) ^ 2 ≤ (2 * (1 + q)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  have hden : (1 + a ^ 2) * (1 + b ^ 2) ≤ 4 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  calc
    _ = 1 / (1 + q) ^ 2 := by simp only [one_div]
    _ ≤ 4 / ((1 + a ^ 2) * (1 + b ^ 2)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
end EisensteinSchwartzPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
end ConcretePrimeRowBridge
end
end OAI
